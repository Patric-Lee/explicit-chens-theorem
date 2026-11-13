import OpenAIGrouped.Unit010
import OpenAIGrouped.Unit008
import OpenAIGrouped.Unit009
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import PrimeNumberTheoremAnd.Wiener
import Mathlib.NumberTheory.AbelSummation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Function.Floor

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceAllocationEnergy.lean; sha256: 95127b9042a0689fb7095f3e338b58eac6d0d9503758f5f3ace89593e6c2e8c2 -/
section Source440
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceAllocationEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
local notation "O" => ActualEisensteinCubic.O

 theorem gaussPolynomial_allocation {α γ : Type*} [Fintype γ]
    (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (b : γ → ℂ) (d : γ → α → ℂ) (z : O) :
    gaussPolynomial S a ha (fun i => ∑ B,b B*d B i) z=
      ∑ B,b B*gaussPolynomial S a ha (d B) z := by
  simp only [gaussPolynomial,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

theorem finite_allocation_energy {α γ : Type*} [Fintype γ]
    (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (b : γ → ℂ) (d : γ → α → ℂ) (rows : Finset O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (hmajor : ∀ z∈rows,1≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (∑ z∈rows,‖gaussPolynomial S a ha (fun i => ∑ B,b B*d B i) z‖^2)≤
      (Fintype.card γ:ℝ)*∑ B,‖b B‖^2*(gaussEnergy S a ha (d B) W K).re := by
  calc
    _ ≤ ∑ z∈rows,(Fintype.card γ:ℝ)*∑ B,‖b B‖^2*‖gaussPolynomial S a ha (d B) z‖^2 := by
      apply Finset.sum_le_sum
      intro z hz
      rw [gaussPolynomial_allocation]
      simpa only [Finset.card_univ,norm_mul,mul_pow] using
        CubicEisenstein.norm_sum_sq_le_card Finset.univ
          (fun B => b B*gaussPolynomial S a ha (d B) z)
    _ = (Fintype.card γ:ℝ)*∑ B,‖b B‖^2*∑ z∈rows,‖gaussPolynomial S a ha (d B) z‖^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      exact mul_le_mul_of_nonneg_left
        (finite_energy_le_gaussEnergy S a ha (d B) W K hK rows hW hmajor) (sq_nonneg _)

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem original_source_allocation_energy {α : Type*}
    (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : C≠0) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (A : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (hCJ : ∀ i,IsCoprime C (Ideal.span {a i}))
    (f : α → ℂ) (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (hmajor : ∀ z∈rows,1≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (∑ z∈rows,‖gaussPolynomial A a ha (fun i =>
      finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*Ideal.span {a i})*f i) z‖^2)≤
      ((actualAllocations S C).card:ℝ)*∑ B : actualAllocations S C,
        ‖frozenCoefficient B C R ν Wslot P‖^2*
          (gaussEnergy A a ha (fun i =>
            finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) (Ideal.span {a i})*f i) W K).re := by
  have hc (i : α) := original_source_column S hS hp C R s (Ideal.span {a i}) hC (ha i).1 (hCJ i) hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
  simp_rw [hc,Finset.sum_mul,mul_assoc]
  simpa only [Fintype.card_coe] using finite_allocation_energy A a ha
    (fun B : actualAllocations S C => frozenCoefficient B C R ν Wslot P)
    (fun B i => finiteColumnCoefficient
      (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) (Ideal.span {a i})*f i)
    rows W K hK hW hmajor

end SevenEighths.CenteredMomentSourceAllocationEnergy

end

end OAI

end Source440

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstIdealFamily.lean; sha256: 7e5b59e01bbb802e9025b0204b396e6694f7debf03b0506a841428b457280314 -/
section Source441
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstIdealFamily
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CanonicalRowCompletion
open CanonicalQuadraticSieve HeckeFamily CenteredMomentHeckeExpansion CenteredMomentSourceRow
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentFirstColumns
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_one_primary (η : Character) (m : O) (t : ℝ)
    (I : Ideal O) (hI : Supported I) :
    rowWeight η m 1 1 t I=elementCoeff η (CompletedGauss.primaryGenerator I)*
      coprimalityMask m (CompletedGauss.primaryGenerator I)*(Ideal.absNorm I:ℂ)^(Complex.I*t) := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := primary_span_supported I hI
  have he : idealCoeff η I=elementCoeff η (CompletedGauss.primaryGenerator I) := by
    have hh := idealCoeff_span η hn
    rw [hs] at hh
    exact hh
  have hm : idealRowHom (m^6) I=coprimalityMask m (CompletedGauss.primaryGenerator I) := by
    have hh := idealRowHom_sixth_eq_mask m _ (hs.symm ▸ hI)
    rw [hs] at hh
    exact hh
  change (idealCoeff η I*idealRowHom (m^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)=_
  rw [mul_one,mul_one,he,hm]

theorem ideal_height_of_primary (η τ : Character) (m : O) (F : O → ℂ)
    (hτ : ∀ n : O,Supported (Ideal.span {n}) → goodLambda^2∣n-1 →
      elementCoeff τ n=elementCoeff η n*coprimalityMask m n*F n)
    (I : Ideal O) (hI : Supported I) (t : ℝ) :
    idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
      rowWeight η m 1 1 t I*F (CompletedGauss.primaryGenerator I) := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := CompletedGauss.primaryGenerator_spec I hn
  have he := hτ (CompletedGauss.primaryGenerator I) (hs.1.symm ▸ hI) hs.2
  rw [← idealCoeff_span τ hn,hs.1] at he
  rw [he,rowWeight_one_primary η m t I hI]
  ring

theorem exists_first_ideal_pair (η : Character) (m : O) (hm : m≠0)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (ξ₁ ξ₂ : RayCharacter) :
    let e := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E
    let r := activeConductor C D
    let ρ := finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    let M := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : Character,τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ I : Ideal O,Supported I → ∀ t : ℝ,
        idealCoeff τ₁ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
          rowWeight η m 1 1 t I*
            (leftCoefficient e r ρ (CompletedGauss.primaryGenerator I)*
              rayCharacter ξ₁ (CompletedGauss.primaryGenerator I))) ∧
      (∀ I : Ideal O,Supported I → ∀ t : ℝ,
        idealCoeff τ₂ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
          rowWeight η m 1 1 t I*
            (rightCoefficient e r ρ (CompletedGauss.primaryGenerator I)*
              rayCharacter ξ₂ (CompletedGauss.primaryGenerator I))) := by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩ := exists_canonical_first_pair η m hm hmLam hm2 C D hC E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,?_,?_⟩
  · intro I hI t
    apply ideal_height_of_primary η τ₁ m
      (fun n => leftCoefficient (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
        (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n*rayCharacter ξ₁ n) _ I hI t
    intro n hn hp
    rw [h₁ n hn hp]
    ring
  · intro I hI t
    apply ideal_height_of_primary η τ₂ m
      (fun n => rightCoefficient (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
        (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n*rayCharacter ξ₂ n) _ I hI t
    intro n hn hp
    rw [h₂ n hn hp]
    ring

end SevenEighths.CenteredMomentFirstIdealFamily

end

end OAI

end Source441

/- Original source: OAI/NumberTheory/DirichletL/Moments/HeckeColumnWindow.lean; sha256: 0ea6c407b7748b6c6abce234c9831803ed61cec1a8487883e0538586b13d0fb8 -/
section Source442
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open MeasureTheory

namespace SevenEighths.CenteredMomentHeckeColumnWindow
open FourierBridge HeckeFamily CenteredMomentSmooth CenteredMomentGaussEnergy
open CenteredMomentTwist
local notation "O" => ActualEisensteinCubic.O

def heightCoeff (τ : Character) (t : ℝ) (I : Ideal O) : ℂ :=
  idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)

theorem heightCoeff_add (τ : Character) (I : Ideal O) (hI : I≠0) (t v : ℝ) :
    heightCoeff τ (t+v) I=heightCoeff τ t I*(Ideal.absNorm I:ℂ)^(Complex.I*v) := by
  have hn : (Ideal.absNorm I:ℂ)≠0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  simp only [heightCoeff,Complex.ofReal_add,mul_add,Complex.cpow_add _ _ hn]
  ring

theorem heightCoeff_phase (τ : Character) (I : Ideal O) (hI : I≠0)
    (t θ X : ℝ) (hX : 0<X) :
    heightCoeff τ t I*logPhase θ (-Real.log ((Ideal.absNorm I:ℝ)/X))=
      logPhase θ (Real.log X)*heightCoeff τ (t-2*Real.pi*θ) I := by
  have hn : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  rw [logPhase_norm_ratio _ X θ hn hX,sub_eq_add_neg,heightCoeff_add τ I hI]
  push_cast
  ring

def rootProfile (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) : 𝓢(ℝ,ℂ) :=
  (hVc.mul_right (f':=fun u : ℝ => (Real.exp (-u/2):ℂ))).toSchwartzMap
    (hVs.mul (Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp (contDiff_id.neg.div_const 2))))

theorem rootProfile_apply (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (u : ℝ) :
    rootProfile V hVc hVs u=rootWindow V u := by
  change V u*(Real.exp (-u/2):ℂ)=_
  rw [rootWindow,← Real.exp_half,show -u/2=-(u/2) by ring,Real.exp_neg,
    Complex.ofReal_inv,div_eq_mul_inv]
  ring

def columnDensity (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) : 𝓢(ℝ,ℂ) :=
  𝓕 (rootProfile V hVc hVs)

theorem columnDensity_moments (V : ℝ → ℂ) (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) (J : ℕ) :
    Integrable (fun w : ℝ => (1+‖w‖)^J*‖columnDensity V hVc hVs w‖) :=
  JointLogSeparation.weighted_schwartz_integrable _ J

theorem rootWindow_integral (V : ℝ → ℂ) (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) (u : ℝ) :
    rootWindow V u=∫ w : ℝ,logPhase w u*columnDensity V hVc hVs w := by
  rw [← rootProfile_apply V hVc hVs u,schwartz_log_inversion]
  apply integral_congr_ae
  filter_upwards [] with w
  congr 2
  simp only [Real.inner_apply]
  push_cast
  ring

theorem phase_combine (w θ u : ℝ) :
    logPhase w u*logPhase θ (-u)=logPhase (θ-w) (-u) := by
  unfold logPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem height_column_integral (V : ℝ → ℂ) (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) (τ : Character) (I : Ideal O) (hI : I≠0)
    (t θ X : ℝ) (hX : 0<X) :
    heightCoeff τ t I*columnPhase V (Real.log ((Ideal.absNorm I:ℝ)/X)) θ=
      ∫ w : ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        heightCoeff τ (t+2*Real.pi*(w-θ)) I := by
  rw [columnPhase,rootWindow_integral V hVc hVs,← mul_assoc,← integral_const_mul,← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with w
  calc
    _ = columnDensity V hVc hVs w*(heightCoeff τ t I*
      (logPhase w (Real.log ((Ideal.absNorm I:ℝ)/X))*
        logPhase θ (-Real.log ((Ideal.absNorm I:ℝ)/X)))) := by ring
    _ = _ := by
      rw [phase_combine,heightCoeff_phase τ I hI t (θ-w) X hX,
        show t-2*Real.pi*(θ-w)=t+2*Real.pi*(w-θ) by ring]
      ring

theorem height_column_integrable (V : ℝ → ℂ) (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) (τ : Character) (I : Ideal O) (hI : I≠0)
    (t θ X : ℝ) (hX : 0<X) :
    Integrable (fun w : ℝ => columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      heightCoeff τ (t+2*Real.pi*(w-θ)) I) := by
  have he (w : ℝ) : logPhase (θ-w) (Real.log X)*heightCoeff τ (t+2*Real.pi*(w-θ)) I=
      heightCoeff τ t I*logPhase (θ-w) (-Real.log ((Ideal.absNorm I:ℝ)/X)) := by
    rw [heightCoeff_phase τ I hI t (θ-w) X hX]
    congr 2
    ring
  have hfun : (fun w : ℝ => columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      heightCoeff τ (t+2*Real.pi*(w-θ)) I) =
      (fun w : ℝ => columnDensity V hVc hVs w*(heightCoeff τ t I*
        logPhase (θ-w) (-Real.log ((Ideal.absNorm I:ℝ)/X)))) := by
    funext w
    rw [mul_assoc,he w]
  rw [hfun]
  apply ((columnDensity V hVc hVs).integrable.norm.const_mul ‖heightCoeff τ t I‖).mono'
  · have hp := (logPhase_continuous_left (-Real.log ((Ideal.absNorm I:ℝ)/X))).comp
      (show Continuous (fun w : ℝ => θ-w) from continuous_const.sub continuous_id)
    exact ((columnDensity V hVc hVs).continuous.mul (hp.const_mul _)).aestronglyMeasurable
  · filter_upwards [] with w
    simp only [norm_mul,logPhase_norm,mul_one]
    exact le_of_eq (mul_comm _ _)

theorem gauss_column_integral {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,CanonicalQuadraticSieve.Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    gaussPolynomial S a ha (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) z=
      ∫ w : ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        gaussPolynomial S a ha (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z := by
  have hi (i : α) : Integrable (fun w : ℝ => β i*
      (columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i}))*gaussRow (a i) (ha i) z) :=
    ((height_column_integrable V hVc hVs τ _ (ha i).1 t θ X hX).const_mul _).mul_const _
  unfold gaussPolynomial
  calc
    _ = ∑ i∈S,∫ w : ℝ,β i*
      (columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i}))*gaussRow (a i) (ha i) z := by
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

end SevenEighths.CenteredMomentHeckeColumnWindow

end

end OAI

end Source442

/- Original source: OAI/NumberTheory/DirichletL/Moments/HeckeWindowEnergy.lean; sha256: 0ba89957b692e5fce86ab510560866efeba801acbaf5a516c7209cf46d95087c -/
section Source443
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentHeckeWindowEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow
open HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

theorem finite_weighted_integral_energy {κ : Type*} [Fintype κ]
    (b : ℝ → ℂ) (φ : κ → ℝ → ℂ) (w : ℝ → ℝ) (hw : ∀ t,0<w t)
    (E : ℝ) (hE : 0≤E) (hb : Integrable (fun t => w t*‖b t‖))
    (hφ : ∀ k,Integrable (fun t => b t*φ k t))
    (hbound : ∀ t,(∑ k,‖φ k t‖^2)≤E*(w t)^2) :
    (∑ k,‖∫ t : ℝ,b t*φ k t‖^2)≤E*(∫ t : ℝ,w t*‖b t‖)^2 := by
  have hn (t : ℝ) : (w t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hw t).ne'
  have hnorm (t : ℝ) : ‖(w t:ℂ)‖=w t := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hw t)]
  have he (k : κ) (t : ℝ) : ((w t:ℂ)*b t)*(φ k t/(w t:ℂ))=b t*φ k t := by
    field_simp [hn t]
  have hh := CompletedGauss.finite_integral_energy_bound
    (fun t => (w t:ℂ)*b t) (fun k t => φ k t/(w t:ℂ)) E hE
    (by simpa only [norm_mul,hnorm] using hb)
    (fun k => by simpa only [he] using hφ k) (fun t => by
      simp only [norm_div,hnorm,div_pow,← Finset.sum_div]
      exact (div_le_iff₀ (sq_pos_of_pos (hw t))).mpr (hbound t))
  simpa only [he,norm_mul,hnorm] using hh

theorem gauss_column_integrable {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    Integrable (fun w : ℝ => columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      gaussPolynomial S a ha (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z) := by
  have hi (i : α) := ((height_column_integrable V hVc hVs τ _ (ha i).1 t θ X hX).const_mul (β i)).mul_const
    (gaussRow (a i) (ha i) z)
  convert integrable_finsetSum S (fun i _ => hi i) using 1
  funext w
  simp only [gaussPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem window_energy_from_shifted {α : Type*}
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X) (rows : Finset O)
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀ w : ℝ,(∑ z∈rows,‖gaussPolynomial S a ha
      (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z‖^2)≤
      E*(1+‖w‖)^(2*J)) :
    (∑ z∈rows,‖gaussPolynomial S a ha (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) z‖^2)≤
      E*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  let φ := fun z : rows => fun w : ℝ => logPhase (θ-w) (Real.log X)*
    gaussPolynomial S a ha (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z
  have hi (z : rows) : Integrable (fun w => columnDensity V hVc hVs w*φ z w) := by
    simpa only [φ,mul_assoc] using gauss_column_integrable S a ha β τ t θ X hX V hVc hVs z
  have hb (w : ℝ) : (∑ z : rows,‖φ z w‖^2)≤E*((1+‖w‖)^J)^2 := by
    simp only [φ,norm_mul,logPhase_norm,one_mul,← pow_mul]
    rw [Finset.sum_coe_sort rows (fun z : O => ‖gaussPolynomial S a ha
      (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z‖^2)]
    simpa only [Nat.mul_comm] using henergy w
  have hh := finite_weighted_integral_energy (columnDensity V hVc hVs) φ
    (fun w => (1+‖w‖)^J) (by intro w;positivity) E hE
    (columnDensity_moments V hVc hVs J) hi hb
  calc
    _ = ∑ z : rows,‖∫ w : ℝ,columnDensity V hVc hVs w*φ z w‖^2 := by
      rw [← Finset.sum_coe_sort rows]
      apply Finset.sum_congr rfl
      intro z hz
      rw [gauss_column_integral S a ha β τ t θ X hX V hVc hVs z]
      simp only [φ,mul_assoc]
    _ ≤ _ := hh

def heightCost (t θ : ℝ) : ℝ := (1+‖t‖+2*Real.pi*‖θ‖)*(1+2*Real.pi)

theorem heightCost_pos (t θ : ℝ) : 0<heightCost t θ := by
  unfold heightCost
  positivity

theorem norm_height_shift (t θ w : ℝ) :
    1+‖t+2*Real.pi*(w-θ)‖≤heightCost t θ*(1+‖w‖) := by
  have hπ : 0≤2*Real.pi := by positivity
  have hn := norm_add_le t (2*Real.pi*(w-θ))
  rw [norm_mul,Real.norm_of_nonneg hπ] at hn
  have hs := norm_sub_le w θ
  have hr : 1+‖t+2*Real.pi*(w-θ)‖≤1+‖t‖+2*Real.pi*‖θ‖+2*Real.pi*‖w‖ := by
    nlinarith
  have hb : 1≤1+‖t‖+2*Real.pi*‖θ‖ := by
    nlinarith [norm_nonneg t,mul_nonneg hπ (norm_nonneg θ)]
  have hw : 0≤2*Real.pi*‖w‖ := by positivity
  calc
    _ ≤ (1+‖t‖+2*Real.pi*‖θ‖)*(1+2*Real.pi*‖w‖) := by nlinarith
    _ ≤ _ := by
      unfold heightCost
      rw [mul_assoc (1+‖t‖+2*Real.pi*‖θ‖) (1+2*Real.pi) (1+‖w‖)]
      apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one hb)
      nlinarith [norm_nonneg w,Real.pi_pos]

theorem window_energy_from_height {α : Type*}
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X) (rows : Finset O)
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀ v : ℝ,(∑ z∈rows,‖gaussPolynomial S a ha
      (fun i => β i*heightCoeff τ v (Ideal.span {a i})) z‖^2)≤E*(1+‖v‖)^(2*J)) :
    (∑ z∈rows,‖gaussPolynomial S a ha (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) z‖^2)≤
      (E*heightCost t θ^(2*J))*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  apply window_energy_from_shifted V hVc hVs J S a ha β τ t θ X hX rows
    (E*heightCost t θ^(2*J)) (mul_nonneg hE (pow_nonneg (heightCost_pos t θ).le _))
  intro w
  calc
    _ ≤ E*(1+‖t+2*Real.pi*(w-θ)‖)^(2*J) := henergy _
    _ ≤ E*(heightCost t θ*(1+‖w‖))^(2*J) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (norm_height_shift t θ w) _) hE
    _ = _ := by rw [mul_pow,mul_assoc]

end SevenEighths.CenteredMomentHeckeWindowEnergy

end

end OAI

end Source443

/- Original source: OAI/NumberTheory/DirichletL/Moments/SmoothedWindowEnergy.lean; sha256: 71fd6d27d1041f1b3e7ebee6ff9b24df7a106605c391168bb9511be1ac486c39 -/
section Source444
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSmoothedWindowEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeWindowEnergy HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

theorem gaussEnergy_hasSum_re {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    HasSum (fun z : O => ‖gaussPolynomial S a ha c z‖^2*
      (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) (gaussEnergy S a ha c U K).re := by
  have hs := Complex.hasSum_re (gaussEnergy_summable S a ha c U K hK).hasSum
  simpa only [gaussEnergy,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hs

theorem finite_weighted_le_gaussEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) (rows : Finset O) :
    (∑ z∈rows,‖gaussPolynomial S a ha c z‖^2*(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)≤
      (gaussEnergy S a ha c U K).re :=
  sum_le_hasSum rows (fun z _ => mul_nonneg (sq_nonneg _) (hU z)) (gaussEnergy_hasSum_re S a ha c U K hK)

theorem smoothed_window_energy_from_shifted {α : Type*}
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀ w : ℝ,(gaussEnergy S a ha
      (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) U K).re≤E*(1+‖w‖)^(2*J)) :
    (gaussEnergy S a ha (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) U K).re≤
      E*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  let u := fun z : O => (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re
  let c := fun i => β i*heightCoeff τ t (Ideal.span {a i})*
    CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ
  have hnorm (z : O) (x : ℂ) : ‖(Real.sqrt (u z):ℂ)*x‖^2=u z*‖x‖^2 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,
      Real.sq_sqrt (hU z)]
  have hfin (rows : Finset O) : (∑ z∈rows,‖gaussPolynomial S a ha c z‖^2*u z)≤
      E*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
    let φ := fun z : rows => fun w : ℝ => (Real.sqrt (u z):ℂ)*
      (logPhase (θ-w) (Real.log X)*gaussPolynomial S a ha
        (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z)
    have hi (z : rows) : Integrable (fun w => columnDensity V hVc hVs w*φ z w) := by
      have h := (gauss_column_integrable S a ha β τ t θ X hX V hVc hVs z).const_mul (Real.sqrt (u z):ℂ)
      convert h using 1
      funext w
      dsimp only [φ]
      ring
    have hb (w : ℝ) : (∑ z : rows,‖φ z w‖^2)≤E*((1+‖w‖)^J)^2 := by
      simp only [φ]
      simp_rw [hnorm]
      simp only [norm_mul,logPhase_norm,one_mul,← pow_mul]
      rw [Finset.sum_coe_sort rows (fun z : O => u z*‖gaussPolynomial S a ha
        (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z‖^2)]
      simpa only [mul_comm,Nat.mul_comm] using
        (finite_weighted_le_gaussEnergy S a ha _ U K hK hU rows).trans (henergy w)
    have hh := finite_weighted_integral_energy (columnDensity V hVc hVs) φ
      (fun w => (1+‖w‖)^J) (by intro w;positivity) E hE (columnDensity_moments V hVc hVs J) hi hb
    have he (z : rows) : (∫ w : ℝ,columnDensity V hVc hVs w*φ z w)=
        (Real.sqrt (u z):ℂ)*gaussPolynomial S a ha c z := by
      rw [show gaussPolynomial S a ha c z=_ from gauss_column_integral S a ha β τ t θ X hX V hVc hVs z,
        ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with w
      dsimp only [φ]
      ring
    simp only [he,hnorm] at hh
    rw [Finset.sum_coe_sort rows (fun z : O => u z*‖gaussPolynomial S a ha c z‖^2)] at hh
    simpa only [mul_comm] using hh
  have hs := gaussEnergy_hasSum_re S a ha c U K hK
  rw [← hs.tsum_eq]
  exact Real.tsum_le_of_sum_le (fun z => mul_nonneg (sq_nonneg _) (hU z)) hfin

theorem smoothed_window_energy_from_height {α : Type*}
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀ v : ℝ,(gaussEnergy S a ha
      (fun i => β i*heightCoeff τ v (Ideal.span {a i})) U K).re≤E*(1+‖v‖)^(2*J)) :
    (gaussEnergy S a ha (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) U K).re≤
      (E*heightCost t θ^(2*J))*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  apply smoothed_window_energy_from_shifted V hVc hVs J S a ha β τ t θ X hX U K hK hU
    (E*heightCost t θ^(2*J)) (mul_nonneg hE (pow_nonneg (heightCost_pos t θ).le _))
  intro w
  calc
    _ ≤ E*(1+‖t+2*Real.pi*(w-θ)‖)^(2*J) := henergy _
    _ ≤ E*(heightCost t θ*(1+‖w‖))^(2*J) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (norm_height_shift t θ w) _) hE
    _ = _ := by rw [mul_pow,mul_assoc]

end SevenEighths.CenteredMomentSmoothedWindowEnergy

end

end OAI

end Source444

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceSmoothedAllocation.lean; sha256: 81eeeb0c9b96a742b4e0db9b95fce0693a2e01abf0fae61e77e2ea3aaf84c649 -/
section Source445
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceSmoothedAllocation
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentSmoothedWindowEnergy
open CenteredMomentSourceAllocationEnergy CenteredMomentSourceLiveColumn
open CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
local notation "O" => ActualEisensteinCubic.O

theorem smoothed_allocation_energy {α γ : Type*} [Fintype γ]
    (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (b : γ → ℂ) (d : γ → α → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (gaussEnergy S a ha (fun i => ∑ B,b B*d B i) W K).re≤
      (Fintype.card γ:ℝ)*∑ B,‖b B‖^2*(gaussEnergy S a ha (d B) W K).re := by
  have hs := gaussEnergy_hasSum_re S a ha (fun i => ∑ B,b B*d B i) W K hK
  rw [← hs.tsum_eq]
  apply Real.tsum_le_of_sum_le (fun z => mul_nonneg (sq_nonneg _) (hW z))
  intro rows
  calc
    _ ≤ ∑ z∈rows,(Fintype.card γ:ℝ)*∑ B,‖b B‖^2*
        (‖gaussPolynomial S a ha (d B) z‖^2*(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) := by
      apply Finset.sum_le_sum
      intro z hz
      have h := mul_le_mul_of_nonneg_right
        (CubicEisenstein.norm_sum_sq_le_card Finset.univ
          (fun B => b B*gaussPolynomial S a ha (d B) z)) (hW z)
      rw [gaussPolynomial_allocation]
      simpa only [Finset.card_univ,norm_mul,mul_pow,Finset.sum_mul,mul_assoc] using h
    _ = (Fintype.card γ:ℝ)*∑ B,‖b B‖^2*
        ∑ z∈rows,‖gaussPolynomial S a ha (d B) z‖^2*(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      exact mul_le_mul_of_nonneg_left
        (finite_weighted_le_gaussEnergy S a ha (d B) W K hK hW rows) (sq_nonneg _)

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem original_source_smoothed_allocation_energy {α : Type*}
    (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : C≠0) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (A : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (hCJ : ∀ i,IsCoprime C (Ideal.span {a i}))
    (f : α → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    :
    (gaussEnergy A a ha (fun i =>
      finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*Ideal.span {a i})*f i) W K).re≤
      ((actualAllocations S C).card:ℝ)*∑ B : actualAllocations S C,
        ‖frozenCoefficient B C R ν Wslot P‖^2*
          (gaussEnergy A a ha (fun i =>
            finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) (Ideal.span {a i})*f i) W K).re := by
  have hc (i : α) := original_source_column S hS hp C R s (Ideal.span {a i}) hC (ha i).1 (hCJ i) hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
  simp_rw [hc,Finset.sum_mul,mul_assoc]
  simpa only [Fintype.card_coe] using smoothed_allocation_energy A a ha
    (fun B : actualAllocations S C => frozenCoefficient B C R ν Wslot P)
    (fun B i => finiteColumnCoefficient
      (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) (Ideal.span {a i})*f i)
    W K hK hW

end SevenEighths.CenteredMomentSourceSmoothedAllocation

end

end OAI

end Source445

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceCommonMask.lean; sha256: 196c3afb2447ed13561dcef7aac09b6a19a101d9d7f925c7d0beedf3de9ad5c9 -/
section Source446
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSourceCommonMask
open ActualEisensteinCubic CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentSourceMass CenteredMomentCompleteCommon
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

 theorem profile_nonzero_masks
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι)
    (hne : profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    IsCoprime (finiteTupleProduct v) R ∧ s∣finiteTupleProduct v := by
  constructor
  · by_contra hn
    exact hne (by simp only [profileCoefficient,hn,ite_false,mul_zero,zero_mul])
  · by_contra hn
    exact hne (by simp only [profileCoefficient,hn,ite_false,mul_zero])

theorem column_nonzero_masks
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O)
    (S : Finset (Tuple ι)) (I : Ideal O)
    (hne : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I≠0) :
    IsCoprime I R ∧ s∣I := by
  obtain ⟨v,hv,hvne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have he := (Finset.mem_filter.mp hv).2
  have hm := profile_nonzero_masks R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v hvne
  rwa [he] at hm

theorem pair_common_masks
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (hs : Squarefree s)
    (S : Finset (Tuple ι)) (I J : Ideal O) (hI : I≠0) (hJ : J≠0)
    (hi : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I≠0)
    (hj : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) J≠0) :
    s∣commonPart I J ∧ s∣commonPart J I ∧
      IsCoprime (commonPart I J) R ∧ IsCoprime (commonPart J I) R := by
  have hmi := column_nonzero_masks R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s S I hi
  have hmj := column_nonzero_masks R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s S J hj
  have hd := squarefree_mask_survives s I J hs hI hJ hmi.2 hmj.2
  exact ⟨hd.2.1,hd.2.2.1,
    hmi.1.of_isCoprime_of_dvd_left (commonPart_dvd I J hI),
    hmj.1.of_isCoprime_of_dvd_left (commonPart_dvd J I hJ)⟩

end SevenEighths.CenteredMomentSourceCommonMask

end

end OAI

end Source446

/- Original source: OAI/NumberTheory/DirichletL/Moments/LiveSupport.lean; sha256: fc59bf94629f91c1c643335b4fca2e2d0e39dc54939e1d22870bb6a77e6d1cba -/
section Source447
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentLiveSupport
open CenteredMomentSourceLiveColumn CenteredMomentSourceLiveAllocation CenteredMomentRemainingBox
open CenteredMomentCommonProfile CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum CenteredMomentFirstSectors CenteredMomentSourceCommonMask
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem restore_frozen (B : Tuple ι) (v : Tuple (liveIndices B)) :
    ∀ i,B (Sum.inl i)≠1 → restoreTuple B v (Sum.inl i)=1 := by
  intro i hi
  simp only [restoreTuple,Sum.elim_inl]
  rw [dite_eq_right (by simpa [liveIndices] using hi)]

theorem restore_product (B : Tuple ι) (v : Tuple (liveIndices B)) :
    finiteTupleProduct (restoreTuple B v)=finiteTupleProduct v := by
  rw [remaining_product B _ (restore_frozen B v),remaining_restore]

theorem restored_original_mem (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I) (C : Ideal O)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (hlabel : B∈allocationLabels S C)
    (v : Tuple (liveIndices B)) (hv : v∈liveBox S B hB) :
    (fun i => B i*restoreTuple B v i)∈Fintype.piFinset S := by
  have hg : ∀ i,B (Sum.inl i)≠1 →
      (1:Ideal O)∈residualPool (B (Sum.inl i)) (hB _) (S (Sum.inl i)) := by
    intro i hi
    rw [mem_residualPool,mul_one]
    exact allocation_frozen_gate S hp C B hlabel i hi
  have hu := restore_mem B (fun i => residualPool (B i) (hB i) (S i)) hg v (by simpa only [liveBox,Fintype.mem_piFinset] using hv)
  apply Fintype.mem_piFinset.mpr
  intro i
  simp only [Fintype.mem_piFinset] at hu
  exact (mem_residualPool _ _ _ _).mp (hu i)

theorem live_column_original_support (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R a : Ideal O)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (hne : finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) a≠0) :
    C*a∈finiteColumns (Fintype.piFinset S) ∧ a≠0 ∧ IsCoprime C a := by
  obtain ⟨v,hv,hvn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hv,ha⟩ := Finset.mem_filter.mp hv
  have hm := profile_nonzero_masks (R*C) (fun i : liveIndices B => ν i.val)
    (fun i => Wslot i.val) (fun i => P i.val) W₁ W₂ X₁ X₂ Y₁ Y₂
    (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1 v hvn
  rw [ha,IsCoprime.mul_right_iff] at hm
  have hsrc := restored_original_mem S hp C B hB hlabel v hv
  have he : finiteTupleProduct (fun i => B i*restoreTuple B v i)=C*a := by
    rw [finiteTupleProduct,Finset.prod_mul_distrib]
    change finiteTupleProduct B*finiteTupleProduct (restoreTuple B v)=_
    rw [hprod,restore_product,ha]
  have hn : C*a≠0 := by
    rw [← he,finiteTupleProduct]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hS i _ (Fintype.mem_piFinset.mp hsrc i))
  exact ⟨Finset.mem_image.mpr ⟨_,hsrc,he⟩,right_ne_zero_of_mul hn,hm.1.2.symm⟩

end SevenEighths.CenteredMomentLiveSupport

end

end OAI

end Source447

/- Original source: OAI/NumberTheory/DirichletL/Moments/LiveDomain.lean; sha256: 9bdeb219b4021cfad192c1294008d31d5e604fec2f23ea1e2d62cb2f1c4606f9 -/
section Source448
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentLiveDomain
open CenteredMomentSourceLiveColumn CenteredMomentLiveSupport CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentFirstSectors CenteredMomentSourceRow CanonicalQuadraticSieve
open CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

 theorem finite_column_mem {ι : Type*} [Fintype ι] (S : Finset (Tuple ι))
    (β : Tuple ι → ℂ) (a : Ideal O) (ha : finiteColumnCoefficient S β a≠0) : a∈finiteColumns S := by
  obtain ⟨v,hv,hvn⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_image.mpr ⟨v,hv,he⟩

 theorem sum_same_support (S T : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (hST : ∀ I∈S,c I≠0 → I∈T) (hTS : ∀ I∈T,c I≠0 → I∈S) :
    (∑ I∈S,c I*f I)=∑ I∈T,c I*f I := by
  have hs : (∑ I∈S∩T,c I*f I)=∑ I∈S,c I*f I := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro I hI hn
    have hc : c I=0 := by
      by_contra h
      exact hn (Finset.mem_inter.mpr ⟨hI,hST I hI h⟩)
    rw [hc,zero_mul]
  have ht : (∑ I∈S∩T,c I*f I)=∑ I∈T,c I*f I := by
    apply Finset.sum_subset Finset.inter_subset_right
    intro I hI hn
    have hc : c I=0 := by
      by_contra h
      exact hn (Finset.mem_inter.mpr ⟨hTS I hI h,hI⟩)
    rw [hc,zero_mul]
  exact hs.symm.trans ht

 theorem supported_residualPool (C : Ideal O) (hC : Supported C) (S : Finset (Ideal O)) :
    supportedColumns (residualPool C hC.1 S)=residualPool C hC.1 (supportedColumns S) := by
  ext I
  simp only [supportedColumns,Finset.mem_filter,mem_residualPool]
  rw [supported_mul_iff]
  tauto

def primaryGaussRow (I : Ideal O) (z : O) : ℂ :=
  if hI : Supported I then
    gaussRow (CompletedGauss.primaryGenerator I)
      (by rw [primary_span_supported I hI];exact hI) z else 0

theorem source_gaussPolynomial (S : Finset (Ideal O)) (c : Ideal O → ℂ) (z : O) :
    gaussPolynomial Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => c I) z=
      ∑ I∈supportedColumns S,c I*primaryGaussRow I z := by
  unfold gaussPolynomial
  rw [← Finset.sum_coe_sort (supportedColumns S) (fun I => c I*primaryGaussRow I z)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [primaryGaussRow,dite_eq_left (Finset.mem_filter.mp I.property).2]
  rfl

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem live_column_sum (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    (∑ I∈supportedColumns (residualPool C hC.1 (finiteColumns (Fintype.piFinset S))),c I*f I)=
      ∑ I∈supportedColumns (finiteColumns (liveBox S B hB)),c I*f I := by
  dsimp only
  apply sum_same_support
  · intro I hI hn
    exact Finset.mem_filter.mpr ⟨finite_column_mem _ _ I hn,(Finset.mem_filter.mp hI).2⟩
  · intro I hI hn
    have hh := live_column_original_support S hS hp B hB C R I hlabel hprod
      ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hn
    exact Finset.mem_filter.mpr ⟨(mem_residualPool C hC.1 _ I).mpr hh.1,(Finset.mem_filter.mp hI).2⟩

theorem live_gaussPolynomial (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ) (z : O) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
    let T := finiteColumns (liveBox S B hB)
    gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q => c I*f I) z=
      gaussPolynomial Finset.univ (sourceGenerator T) (sourceGenerator_supported T)
        (fun I : supportedColumns T => c I*f I) z := by
  let c := finiteColumnCoefficient (liveBox S B hB)
    (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
  let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
  let T := finiteColumns (liveBox S B hB)
  change gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I : supportedColumns Q => c I*f I) z=_
  refine (source_gaussPolynomial Q (fun I => c I*f I) z).trans ?_
  refine Eq.trans ?_ (source_gaussPolynomial T (fun I => c I*f I) z).symm
  simpa only [mul_assoc] using live_column_sum S hS hp B hB C R hC hlabel hprod ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ (fun I => f I*primaryGaussRow I z)

theorem live_gaussEnergy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
    let T := finiteColumns (liveBox S B hB)
    gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q => c I*f I) W K=
      gaussEnergy Finset.univ (sourceGenerator T) (sourceGenerator_supported T)
        (fun I : supportedColumns T => c I*f I) W K := by
  dsimp only
  unfold gaussEnergy
  apply tsum_congr
  intro z
  exact congrArg (fun x : ℂ => ((‖x‖^2:ℝ):ℂ)*W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K))
    (live_gaussPolynomial S hS hp B hB C R hC hlabel hprod ν Wslot P W₁ W₂
      X₁ X₂ Y₁ Y₂ B₁ B₂ f z)

end SevenEighths.CenteredMomentLiveDomain

end

end OAI

end Source448

/- Original source: OAI/NumberTheory/DirichletL/Moments/OriginalChildEnergy.lean; sha256: a8a78f6ccd2f0f96990938c6fde56ae1dfb2643b5a5cea34fe2539f08b4de26c -/
section Source449
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentOriginalChildEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentSourceRow
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
open CenteredMomentLiveSupport CenteredMomentLiveDomain CenteredMomentSourceSmoothedAllocation
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem original_source_punctured_column (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s I : Ideal O) (hC : C≠0) (hI : I≠0) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    (if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0)=
      ∑ B : actualAllocations S C,frozenCoefficient B C R ν Wslot P*
        finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
          (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I := by
  by_cases hc : IsCoprime C I
  · rw [ite_eq_left hc]
    exact original_source_column S hS hp C R s I hC hI hc hsC ν Wslot P W₁ W₂
      X₁ X₂ Y₁ Y₂ B₁ B₂
  · rw [ite_eq_right hc]
    symm
    apply Finset.sum_eq_zero
    intro B hB
    have hz : finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
        (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I=0 := by
      by_contra hn
      exact hc (live_column_original_support S hS hp B
        (allocation_data S C B (Finset.mem_filter.mp B.property).1).1 C R I
        (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
        ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hn).2.2
    rw [hz,mul_zero]

def sourceGaussEnergy (Q : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I : supportedColumns Q => c I*f I) W K

theorem original_child_energy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (f : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (sourceGaussEnergy (residualPool C hC.1 (finiteColumns (Fintype.piFinset S)))
      (fun I => if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0) f W K).re≤
      ((actualAllocations S C).card:ℝ)*∑ B : actualAllocations S C,
        ‖frozenCoefficient B C R ν Wslot P‖^2*
          (sourceGaussEnergy
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K).re := by
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
  have h := smoothed_allocation_energy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) b d W K hK hW
  have he' := funext he
  change (gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) _ W K).re≤_
  rw [he']
  apply h.trans_eq
  rw [Fintype.card_coe]
  apply congrArg (fun x : ℝ => ((actualAllocations S C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  simpa only [b,d,sourceGaussEnergy] using
    congrArg (fun x : ℂ => ‖frozenCoefficient B C R ν Wslot P‖^2*x.re)
    (live_gaussEnergy S hS hp B
    (allocation_data S C B (Finset.mem_filter.mp B.property).1).1 C R hC
    (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ f W K)

end SevenEighths.CenteredMomentOriginalChildEnergy

end

end OAI

end Source449

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondSourceEnergy.lean; sha256: 1828f5356c3ee48438f1f776043909e4a7aa16527f72a134aad5373b2ffb976e -/
section Source450
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSourceEnergy
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentLiveDomain
open CenteredMomentOriginalChildEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentFirstSectors CenteredMomentCommonSectors IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

def secondSourceKernel (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑' h : O,(primaryGaussRow I h*star (primaryGaussRow J h))*
    W (‖ConcreteTraceCRT.eisEmbedding h‖^2/K)

theorem heightCoeff_mul (τ : Character) (t : ℝ) (I J : Ideal O) :
    heightCoeff τ t (I*J)=heightCoeff τ t I*heightCoeff τ t J := by
  have hpow : ((Ideal.absNorm I:ℂ)*(Ideal.absNorm J:ℂ))^(Complex.I*t)=
      (Ideal.absNorm I:ℂ)^(Complex.I*t)*(Ideal.absNorm J:ℂ)^(Complex.I*t) := by
    exact_mod_cast Complex.mul_cpow_ofReal_nonneg
      (Nat.cast_nonneg (Ideal.absNorm I):(0:ℝ)≤Ideal.absNorm I)
      (Nat.cast_nonneg (Ideal.absNorm J):(0:ℝ)≤Ideal.absNorm J) (Complex.I*t)
  simp only [heightCoeff,map_mul,Nat.cast_mul,hpow]
  ring

theorem source_energy_common_sectors (τ : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    sourceGaussEnergy S β (heightCoeff τ t) W K=
      ∑ p∈commonLabels (supportedColumns S) (supportedColumns S),
        ∑ q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
          ((β q.1*heightCoeff τ t q.1)*star (β q.2*heightCoeff τ t q.2))*
            secondSourceKernel q.1 q.2 W K := by
  rw [sourceGaussEnergy,gaussEnergy_expand _ _ _ _ W K hK]
  have hk (I J : supportedColumns S) :
      (∑' h : O,(gaussRow (sourceGenerator S I) (sourceGenerator_supported S I) h*
        star (gaussRow (sourceGenerator S J) (sourceGenerator_supported S J) h))*
          W (‖ConcreteTraceCRT.eisEmbedding h‖^2/K))=secondSourceKernel I J W K := by
    unfold secondSourceKernel
    apply tsum_congr
    intro h
    simp only [primaryGaussRow,dite_eq_left (Finset.mem_filter.mp I.property).2,
      dite_eq_left (Finset.mem_filter.mp J.property).2,sourceGenerator]
  simp_rw [hk]
  let F := fun I J : Ideal O =>
    ((β I*heightCoeff τ t I)*star (β J*heightCoeff τ t J))*secondSourceKernel I J W K
  change (∑ I : supportedColumns S,∑ J : supportedColumns S,F I J)=_
  have he (I : Ideal O) : (∑ J : supportedColumns S,F I J)=∑ J∈supportedColumns S,F I J :=
    Finset.sum_coe_sort (supportedColumns S) (F I)
  simp_rw [he]
  rw [Finset.sum_coe_sort (supportedColumns S) (fun I => ∑ J∈supportedColumns S,F I J)]
  exact sum_common_sectors _ _ _

theorem source_sector_independent_columns (τ : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C D : Ideal O)
    (hC : C≠0) (hD : D≠0) (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((β q.1*heightCoeff τ t q.1)*star (β q.2*heightCoeff τ t q.2))*secondSourceKernel q.1 q.2 W K)=
      heightCoeff τ t C*star (heightCoeff τ t D)*
        ∑ a∈residualPool C hC (supportedColumns S),∑ b∈residualPool D hD (supportedColumns S),
          if IsCoprime C a ∧ IsCoprime C b ∧ IsCoprime a b then
            ((β (C*a)*heightCoeff τ t a)*star (β (D*b)*heightCoeff τ t b))*
              secondSourceKernel (C*a) (D*b) W K else 0 := by
  rw [pairSector_double_sum C D hC hD hCD _ _
    (fun I hI => (Finset.mem_filter.mp hI).2.1)
    (fun I hI => (Finset.mem_filter.mp hI).2.1)
    (fun I J => ((β I*heightCoeff τ t I)*star (β J*heightCoeff τ t J))*secondSourceKernel I J W K),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp only [heightCoeff_mul,star_mul,mul_zero]
  ring

end SevenEighths.CenteredMomentSecondSourceEnergy

end

end OAI

end Source450

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondSourcePoisson.lean; sha256: 2415598acfbc57eaa314587597b3e4d6d3eaaa172daeb860169a23f321462764 -/
section Source451
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSourcePoisson
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentLiveDomain
open CenteredMomentOriginalChildEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentFourier CenteredMomentPoisson
open CenteredMomentSecondSourceEnergy CenteredMomentSupportedCorrelation CenteredMomentRowNorm
local notation "O" => ActualEisensteinCubic.O

theorem secondSourceKernel_poisson (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    secondSourceKernel I J W K=
      (K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))*
        ∑' h : O,actualCorrelation (primaryGenerator I) (primaryGenerator J)
          (by rw [primary_span_supported I hI];exact hI)
          (by rw [primary_span_supported J hJ];exact hJ) (-h)*
          paperRadialFourier W (K*‖eisEmbedding h‖^2/
            ‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2) := by
  unfold secondSourceKernel
  simp only [primaryGaussRow,dite_eq_left hI,dite_eq_left hJ,gaussRow]
  rw [sextic_gauss_pair_poisson _ _ ((supported_span_primaryGenerator_iff I).mpr hI)
    ((supported_span_primaryGenerator_iff J).mpr hJ) W K hK]
  simp only [primary_span_supported I hI,primary_span_supported J hJ]

theorem sourceGaussEnergy_poisson (τ : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    sourceGaussEnergy S β (heightCoeff τ t) W K=
      ∑ I : supportedColumns S,∑ J : supportedColumns S,
        ((β I*heightCoeff τ t I)*star (β J*heightCoeff τ t J))*
          ((K:ℂ)/((Real.sqrt (Ideal.absNorm (I:Ideal O):ℝ):ℂ)*(Real.sqrt (Ideal.absNorm (J:Ideal O):ℝ):ℂ)))*
            ∑' h : O,actualCorrelation (sourceGenerator S I) (sourceGenerator S J)
              (sourceGenerator_supported S I) (sourceGenerator_supported S J) (-h)*
              paperRadialFourier W (K*‖eisEmbedding h‖^2/
                ‖eisEmbedding (sourceGenerator S I*sourceGenerator S J)‖^2) := by
  rw [sourceGaussEnergy,gaussEnergy_poisson _ _ _ _ W K hK]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2,
    primary_span_supported J (Finset.mem_filter.mp J.property).2]
  ring

end SevenEighths.CenteredMomentSecondSourcePoisson

end

end OAI

end Source451

/- Original source: OAI/NumberTheory/DirichletL/Moments/PlainEnergy.lean; sha256: 6314ca7721d52278d3e88513d6a844835384dcf8195b205f31915c2723bf94e0 -/
section Source452
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentPlainEnergy
open CanonicalQuadraticSieve CenteredMomentRowNorm ConcreteTraceCRT
open CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O

theorem rowEnergy_summable {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O => ((‖rowPolynomial S a c z‖^2 : ℝ) : ℂ) *
      W (‖eisEmbedding z‖^2/K)) := by
  have hs (i j : α) := (row_pair_summable (a i) (a j) (ha i) (ha j) W K hK).mul_left
    (c i * star (c j))
  simp only [mul_assoc] at hs
  simp only [rowPolynomial_norm_sq,Finset.sum_mul,mul_assoc]
  exact (hasSum_sum (fun i _ => (hasSum_sum (fun j _ => (hs i j).hasSum)))).summable

theorem finite_energy_le_rowEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hW : ∀ z : O, 0 ≤ (W (‖eisEmbedding z‖^2/K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖eisEmbedding z‖^2/K)).re) :
    (∑ z ∈ rows, ‖rowPolynomial S a c z‖^2) ≤ (rowEnergy S a c W K).re := by
  have hs := Complex.hasSum_re (rowEnergy_summable S a ha c W K hK).hasSum
  change HasSum _ (rowEnergy S a c W K).re at hs
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hs
  calc
    _ ≤ ∑ z ∈ rows, ‖rowPolynomial S a c z‖^2*(W (‖eisEmbedding z‖^2/K)).re := by
      apply Finset.sum_le_sum
      intro z hz
      exact le_mul_of_one_le_right (sq_nonneg _) (hmajor z hz)
    _ ≤ _ := sum_le_hasSum rows (fun z _ => mul_nonneg (sq_nonneg _) (hW z)) hs

theorem finite_negative_energy_le_rowEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hW : ∀ z : O, 0 ≤ (W (‖eisEmbedding z‖^2/K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖eisEmbedding z‖^2/K)).re) :
    (∑ z ∈ rows, ‖rowPolynomial S a c (-z)‖^2) ≤ (rowEnergy S a c W K).re := by
  have he := finite_energy_le_rowEnergy S a ha c W K hK (rows.image Neg.neg) hW (by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    simpa only [map_neg,norm_neg] using hmajor w hw)
  rwa [Finset.sum_image (fun x hx y hy hxy => neg_injective hxy)] at he

end SevenEighths.CenteredMomentPlainEnergy

end

end OAI

end Source452

/- Original source: OAI/NumberTheory/DirichletL/Moments/PlainChildEnergy.lean; sha256: c03041b409b0ed173fa4b2b1ae00f6075b51d8f3dcc088e5e554a9a64008ea9b -/
section Source453
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentPlainChildEnergy
open CanonicalQuadraticSieve CanonicalRowCompletion CenteredMomentRowNorm CenteredMomentPlainEnergy CenteredMomentCauchy
open CenteredMomentSmooth
local notation "O" => ActualEisensteinCubic.O

theorem leftColumn_eq_rowPolynomial {α : Type*} (S : Finset α) (a : α → O)
    (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (z : O) (t : ℝ) :
    leftColumn S (fun i => c i * idealRowHom z (Ideal.span {a i})) V u t =
      rowPolynomial S a (fun i => c i * columnPhase V (u i) t) z := by
  unfold leftColumn rowPolynomial
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem rightColumn_eq_star_rowPolynomial {α : Type*} (S : Finset α) (a : α → O)
    (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (z : O) (t : ℝ) :
    rightColumn S (fun i => c i * idealRowHom z (Ideal.span {a i})) V u t =
      star (rowPolynomial S a (fun i => c i * star (columnPhase V (u i) t)) z) := by
  simp only [rightColumn, rowPolynomial, star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem whole_kernel_plain_child_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (a : α → O) (b : β → O)
        (_ha : ∀ i, Supported (Ideal.span {a i}))
        (_hb : ∀ j, Supported (Ideal.span {b j}))
        (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ) (η : O → ℂ),
      (∀ z ∈ rows, ‖η z‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      ∀ E₁ E₂ : ℝ, 0 ≤ E₁ → 0 ≤ E₂ →
      (∀ t : ℝ, (rowEnergy S a (fun i => c i * columnPhase (V 2) (u i) t) U K).re ≤
        (E₁ * (1 + ‖t‖) ^ J₁) ^ 2) →
      (∀ t : ℝ, (rowEnergy T b (fun j => d j * star (columnPhase (V 3) (v j) t)) U K).re ≤
        (E₂ * (1 + ‖t‖) ^ J₂) ^ 2) →
      (1 + R) ^ A * ‖∑ z ∈ rows, η z *
        (∑ i ∈ S, ∑ j ∈ T,
          ((c i * idealRowHom z (Ideal.span {a i})) * star (d j * idealRowHom (-z) (Ideal.span {b j}))) *
            wholeKernel W V R (ρ z) (x z) (u i) (v j))‖ ≤ C * (E₁ * E₂) := by
  obtain ⟨C, hC, hbound⟩ := whole_kernel_row_estimate W V M hM hV A (J₁ + J₂)
  refine ⟨C, hC, ?_⟩
  intro R hR α β rows S T a b ha hb c d u v ρ x η hη hV₀ hV₁ U K hK hU hmajor
    E₁ E₂ hE₁ hE₂ hleft hright
  apply hbound R hR rows S T
    (fun z i => c i * idealRowHom z (Ideal.span {a i}))
    (fun z j => d j * idealRowHom (-z) (Ideal.span {b j})) u v ρ x η hη hV₀ hV₁
    (E₁ * E₂) (mul_nonneg hE₁ hE₂)
  intro t
  have hL := (finite_energy_le_rowEnergy S a ha
    (fun i => c i * columnPhase (V 2) (u i) t) U K hK rows hU hmajor).trans (hleft t)
  have hR' := (finite_negative_energy_le_rowEnergy T b hb
    (fun j => d j * star (columnPhase (V 3) (v j) t)) U K hK rows hU hmajor).trans (hright t)
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

end SevenEighths.CenteredMomentPlainChildEnergy

end

end OAI

end Source453

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondDescent.lean; sha256: 5208e01f67df6a509688af29269f9e6e0987cddc5b4f3c5fd0727016c1deb6b1 -/
section Source454
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondDescent
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentFixedRay
open CenteredMomentRowNorm CenteredMomentSmooth CenteredMomentPlainChildEnergy RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

private theorem weighted_norm_sum {α : Type*} (S : Finset α) (a f : α → ℂ)
    (r : ℝ) (hr : 0 ≤ r) (B : α → ℝ)
    (hB : ∀ i ∈ S, r*‖f i‖ ≤ B i) :
    r*‖∑ i ∈ S, a i*f i‖ ≤ ∑ i ∈ S, ‖a i‖*B i := by
  calc
    _ ≤ r*∑ i ∈ S, ‖a i*f i‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hr
    _ = ∑ i ∈ S, ‖a i‖*(r*‖f i‖) := by simp only [Finset.mul_sum,norm_mul]; congr 1; funext i; ring
    _ ≤ _ := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hB i hi) (norm_nonneg _))

theorem actual_row_children {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
    (D E : O) (a : α → O) (b : β → O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j}))
    (hpD : ConcretePrimeRowBridge.goodLambda^2 ∣ D-1)
    (hpE : ConcretePrimeRowBridge.goodLambda^2 ∣ E-1)
    (hpa : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1)
    (hpb : ∀ j, ConcretePrimeRowBridge.goodLambda^2 ∣ b j-1)
    (hcopA : ∀ i, IsCoprime (D*E) (a i)) (hcopB : ∀ j, IsCoprime (D*E) (b j))
    (q : O → ℂ) (c : α → ℂ) (d : β → ℂ) (K : O → α → β → ℂ) :
    (∑ z ∈ rows, q z * ∑ i ∈ S, ∑ j ∈ T,
      (if IsCoprime (a i) (b j) then
        actualCorrelation (D*a i) (E*b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) z
        else 0) * (c i*star (d j))*K z i j) =
      ∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
        (UniqueFactorizationMonoid.moebius L : ℂ) *
          ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (phaseTable D E) χ ξ *
            ∑ z ∈ rows, (q z*actualCorrelation D E hD hE z) *
              ∑ i ∈ S, ∑ j ∈ T,
                ((divisorCoefficient L a c χ i*idealRowHom z (Ideal.span {a i})) *
                  star (divisorCoefficient L b d (ξ⁻¹) j*idealRowHom (-z) (Ideal.span {b j}))) * K z i j := by
  simp_rw [finite_correlation_children S T D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro L hL
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro ξ hξ
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem finite_ray_divisor_bound (L : Finset (Ideal O)) (D E : O)
    (F : Ideal O → RayCharacter → RayCharacter → ℂ)
    (r C : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C) (B₁ B₂ : Ideal O → ℝ)
    (hB₁ : ∀ I ∈ L, 0 ≤ B₁ I) (hB₂ : ∀ I ∈ L, 0 ≤ B₂ I)
    (hF : ∀ I ∈ L, ∀ χ ξ, r*‖F I χ ξ‖ ≤ C*(B₁ I*B₂ I)) :
    r*‖∑ I ∈ L, (UniqueFactorizationMonoid.moebius I : ℂ)*
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (phaseTable D E) χ ξ * F I χ ξ‖ ≤
      (256*C)*∑ I ∈ L, ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖*(B₁ I*B₂ I) := by
  have he (I : Ideal O) (hI : I ∈ L) :
      r*‖∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff (phaseTable D E) χ ξ*F I χ ξ‖ ≤ (256*C)*(B₁ I*B₂ I) := by
    calc
      _ ≤ ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          ‖pairCoeff (phaseTable D E) χ ξ‖*(C*(B₁ I*B₂ I)) := by
        have h := weighted_norm_sum Finset.univ (fun _ : RayCharacter => (1 : ℂ))
          (fun χ => ∑ ξ : RayCharacter, pairCoeff (phaseTable D E) χ ξ*F I χ ξ) r hr
          (fun χ => ∑ ξ : RayCharacter, ‖pairCoeff (phaseTable D E) χ ξ‖*(C*(B₁ I*B₂ I)))
          (fun χ _ => weighted_norm_sum Finset.univ _ _ r hr _ (fun ξ _ => hF I hI χ ξ))
        simpa only [one_mul,norm_one] using h
      _ = (∑ χ : RayCharacter, ∑ ξ : RayCharacter, ‖pairCoeff (phaseTable D E) χ ξ‖)*
          (C*(B₁ I*B₂ I)) := by simp only [Finset.sum_mul]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right (phaseTable_mass D E)
          (mul_nonneg hC (mul_nonneg (hB₁ I hI) (hB₂ I hI)))
        convert h using 1 ; ring
  have h := weighted_norm_sum L (fun I => (UniqueFactorizationMonoid.moebius I : ℂ))
    (fun I => ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (phaseTable D E) χ ξ*F I χ ξ)
    r hr (fun I => (256*C)*(B₁ I*B₂ I)) he
  convert h using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  ring

theorem whole_kernel_actual_second_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (D E : O) (a : α → O) (b : β → O)
        (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
        (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j})),
      (ConcretePrimeRowBridge.goodLambda^2 ∣ D-1) →
      (ConcretePrimeRowBridge.goodLambda^2 ∣ E-1) →
      (∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1) →
      (∀ j, ConcretePrimeRowBridge.goodLambda^2 ∣ b j-1) →
      (∀ i, IsCoprime (D*E) (a i)) → (∀ j, IsCoprime (D*E) (b j)) →
      ∀ (q : O → ℂ) (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ),
      (∀ z ∈ rows, ‖q z*actualCorrelation D E hD hE z‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      ∀ (B₁ B₂ : Ideal O → ℝ),
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₁ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₂ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ χ : RayCharacter, ∀ t : ℝ,
        (rowEnergy S a (fun i => divisorCoefficient L a c χ i*columnPhase (V 2) (u i) t) U K).re ≤
          (B₁ L*(1+‖t‖)^J₁)^2) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ ξ : RayCharacter, ∀ t : ℝ,
        (rowEnergy T b (fun j => divisorCoefficient L b d ξ j*star (columnPhase (V 3) (v j) t)) U K).re ≤
          (B₂ L*(1+‖t‖)^J₂)^2) →
      (1+R)^A * ‖∑ z ∈ rows, q z * ∑ i ∈ S, ∑ j ∈ T,
        (if IsCoprime (a i) (b j) then
          actualCorrelation (D*a i) (E*b j)
            (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) z
          else 0) * (c i*star (d j))*wholeKernel W V R (ρ z) (x z) (u i) (v j)‖ ≤
        C*∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
          ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖*(B₁ L*B₂ L) := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_plain_child_bound W V M hM hV A J₁ J₂
  refine ⟨256*C,mul_nonneg (by norm_num) hC,?_⟩
  intro R hR α β rows S T D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB
    q c d u v ρ x hq hV₀ hV₁ U K hK hU hmajor B₁ B₂ hB₁ hB₂ hleft hright
  rw [actual_row_children rows S T D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB]
  apply finite_ray_divisor_bound _ D E _ ((1+R)^A) C (by positivity) hC B₁ B₂ hB₁ hB₂
  intro L hL χ ξ
  exact hbound R hR rows S T a b ha hb
    (divisorCoefficient L a c χ) (divisorCoefficient L b d (ξ⁻¹)) u v ρ x
    (fun z => q z*actualCorrelation D E hD hE z) hq hV₀ hV₁ U K hK hU hmajor
    (B₁ L) (B₂ L) (hB₁ L hL) (hB₂ L hL) (hleft L hL χ) (hright L hL (ξ⁻¹))

end SevenEighths.CenteredMomentSecondDescent

end

end OAI

end Source454

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondScaled.lean; sha256: 401fad97f9c653419b699cbf92f23276fee9fdeb623da533179d7402b7d3ae93 -/
section Source455
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondScaled
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentFixedRay
open CenteredMomentRowNorm CenteredMomentSmooth CenteredMomentPlainChildEnergy RayFourExpansion
open CenteredMomentSecondDescent CenteredMomentProductCRT CenteredMomentUnequal CenteredMomentPartition
local notation "O" => ActualEisensteinCubic.O

def movingCoefficient {α : Type*} (A : O) (a : α → O) (c : α → ℂ) (i : α) : ℂ :=
  c i*idealRowHom A (Ideal.span {a i})

theorem divisorCoefficient_moving {α : Type*} (L : Ideal O) (A : O) (a : α → O)
    (c : α → ℂ) (χ : RayCharacter) (i : α) :
    divisorCoefficient L a (movingCoefficient A a c) χ i =
      divisorCoefficient L a c χ i*idealRowHom A (Ideal.span {a i}) := by
  unfold divisorCoefficient movingCoefficient
  split_ifs <;> ring

theorem actual_child_column {α : Type*} (L : Ideal O) (η : HeckeFamily.Character)
    (χ : RayCharacter) (m A₀ h : O) (a : α → O) (β : α → ℂ) (i : α)
    (ha : Supported (Ideal.span {a i}))
    (hp : ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1) :
    divisorCoefficient L a (movingCoefficient A₀ a
      (fun j => β j*HeckeFamily.elementCoeff η (a j)*coprimalityMask m (a j))) χ i *
      idealRowHom h (Ideal.span {a i}) =
    (if L ∣ Ideal.span {a i} then β i else 0) *
      rowTwist (HeckeRowClosure.elementHom (CenteredMomentChildRows.childCharacter η χ))
        m 1 (A₀*h) (a i) := by
  rw [CenteredMomentChildRows.child_row_primary η χ m A₀ h (a i) ha hp]
  simp only [divisorCoefficient,movingCoefficient,idealRowHom_argument_mul]
  split_ifs <;> ring

theorem scaled_partition_scalar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, Supported (Ideal.span {p i}))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime p))
    (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (U : Finset ι) (part : O → Prop) (V₀ h : O)
    (hpart : part (V₀*h) → ∀ i ∈ U, c i=d i ∧ ¬6∣c i ∧
      ¬p i∣CenteredMomentPartition.dividedFrequency p c d (V₀*h) i) :
    ‖(if part (V₀*h) then (1:ℂ)/(CenteredMomentPartition.partitionNormalizer p c d U : ℂ) else 0) *
      actualCorrelation (∏ i, p i^c i) (∏ i, p i^d i)
        (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
        (supported_product _ (fun i => supported_power (p i) (hp i) (d i)))
        (((∏ i, p i^min (c i) (d i))*V₀)*h)‖ ≤ 1 := by
  have hb := CenteredMomentPartition.normalized_partition_norm_le_one
    p hp hg hchar hcop c d hc hd U part (V₀*h) hpart
  by_cases hh : part (V₀*h)
  · simpa only [ite_eq_left hh,one_div,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm,one_mul] using hb
  · simp only [ite_eq_right hh,zero_mul,norm_zero,zero_le_one]

theorem actual_scaled_row_children {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
    (D E A₀ : O) (a : α → O) (b : β → O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j}))
    (hpD : ConcretePrimeRowBridge.goodLambda^2 ∣ D-1)
    (hpE : ConcretePrimeRowBridge.goodLambda^2 ∣ E-1)
    (hpa : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1)
    (hpb : ∀ j, ConcretePrimeRowBridge.goodLambda^2 ∣ b j-1)
    (hcopA : ∀ i, IsCoprime (D*E) (a i)) (hcopB : ∀ j, IsCoprime (D*E) (b j))
    (q : O → ℂ) (c : α → ℂ) (d : β → ℂ) (K : O → α → β → ℂ) :
    (∑ z ∈ rows, q z * ∑ i ∈ S, ∑ j ∈ T,
      (if IsCoprime (a i) (b j) then
        actualCorrelation (D*a i) (E*b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) (A₀*z)
        else 0) * (c i*star (d j))*K z i j) =
      ∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
        (UniqueFactorizationMonoid.moebius L : ℂ) *
          ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (phaseTable D E) χ ξ *
            ∑ z ∈ rows, (q z*actualCorrelation D E hD hE (A₀*z)) *
              ∑ i ∈ S, ∑ j ∈ T,
                ((divisorCoefficient L a (movingCoefficient A₀ a c) χ i*idealRowHom z (Ideal.span {a i})) *
                  star (divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹) j*idealRowHom (-z) (Ideal.span {b j}))) * K z i j := by
  simp_rw [finite_correlation_children S T D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro L hL
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro ξ hξ
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show -(A₀*z)=A₀*(-z) by ring]
  simp only [idealRowHom_argument_mul,divisorCoefficient_moving,star_mul]
  ring

theorem whole_kernel_scaled_second_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
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
        (ρ x : O → ℝ),
      (∀ z ∈ rows, ‖q z*actualCorrelation D E hD hE (A₀*z)‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      ∀ (B₁ B₂ : Ideal O → ℝ),
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₁ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₂ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ χ : RayCharacter, ∀ t : ℝ,
        (rowEnergy S a (fun i => divisorCoefficient L a (movingCoefficient A₀ a c) χ i*columnPhase (V 2) (u i) t) U K).re ≤
          (B₁ L*(1+‖t‖)^J₁)^2) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ ξ : RayCharacter, ∀ t : ℝ,
        (rowEnergy T b (fun j => divisorCoefficient L b (movingCoefficient A₀ b d) ξ j*star (columnPhase (V 3) (v j) t)) U K).re ≤
          (B₂ L*(1+‖t‖)^J₂)^2) →
      (1+R)^A * ‖∑ z ∈ rows, q z * ∑ i ∈ S, ∑ j ∈ T,
        (if IsCoprime (a i) (b j) then
          actualCorrelation (D*a i) (E*b j)
            (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) (A₀*z)
          else 0) * (c i*star (d j))*wholeKernel W V R (ρ z) (x z) (u i) (v j)‖ ≤
        C*∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
          ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖*(B₁ L*B₂ L) := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_plain_child_bound W V M hM hV A J₁ J₂
  refine ⟨256*C,mul_nonneg (by norm_num) hC,?_⟩
  intro R hR α β rows S T D E A₀ a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB
    q c d u v ρ x hq hV₀ hV₁ U K hK hU hmajor B₁ B₂ hB₁ hB₂ hleft hright
  rw [actual_scaled_row_children rows S T D E A₀ a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB]
  apply finite_ray_divisor_bound _ D E _ ((1+R)^A) C (by positivity) hC B₁ B₂ hB₁ hB₂
  intro L hL χ ξ
  exact hbound R hR rows S T a b ha hb
    (divisorCoefficient L a (movingCoefficient A₀ a c) χ) (divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹)) u v ρ x
    (fun z => q z*actualCorrelation D E hD hE (A₀*z)) hq hV₀ hV₁ U K hK hU hmajor
    (B₁ L) (B₂ L) (hB₁ L hL) (hB₂ L hL) (hleft L hL χ) (hright L hL (ξ⁻¹))

end SevenEighths.CenteredMomentSecondScaled

end

end OAI

end Source455

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondSectorColumns.lean; sha256: e68433440a4791d396c15ba9ffa78f1748681025e42cf59f7a68fe44726235a0 -/
section Source456
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSectorColumns
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondSourceEnergy
open CenteredMomentFirstSectors CenteredMomentFirstSectorTransform CenteredMomentCommonSectors
open CenteredMomentSecondScaled CenteredMomentSupportedCorrelation CenteredMomentChildAssembly
open CenteredMomentFixedRay CenteredMomentMobiusRegroup RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

def sectorPool (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O)) : Finset (Ideal O) :=
  (residualPool C hC (supportedColumns S)).filter (IsCoprime C)

theorem sectorPool_supported (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : Supported (a:Ideal O) :=
  residualPool_supported C hC S ⟨a,(Finset.mem_filter.mp a.property).1⟩

def sectorElement (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : O := primaryGenerator a

theorem sectorElement_span (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : Ideal.span {sectorElement C hC S a}=a :=
  primary_span_supported a (sectorPool_supported C hC S a)

theorem sectorElement_supported (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : Supported (Ideal.span {sectorElement C hC S a}) := by
  rw [sectorElement_span]
  exact sectorPool_supported C hC S a

theorem sectorElement_primary (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : ConcretePrimeRowBridge.goodLambda^2∣sectorElement C hC S a-1 :=
  (primaryGenerator_spec a (supported_primaryGenerator_ne_zero a (sectorPool_supported C hC S a))).2

theorem coprime_of_same_support (C D a : Ideal O) (hC : C≠0) (hD : D≠0) (ha : a≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    IsCoprime C a ↔ IsCoprime D a := by
  change IdealMobiusDivisorSum.primeSupport C=IdealMobiusDivisorSum.primeSupport D at hCD
  rw [←IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC ha,
    ←IdealCoprimeSieveOperator.primeSupport_disjoint_iff hD ha,hCD]

theorem sectorElement_coprime (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (S : Finset (Ideal O)) (a : sectorPool C hC.1 S) :
    IsCoprime (primaryGenerator C*primaryGenerator D) (sectorElement C hC.1 S a) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [←Ideal.span_singleton_mul_span_singleton,primary_span_supported C hC,
    primary_span_supported D hD,sectorElement_span]
  have hc := (Finset.mem_filter.mp a.property).2
  exact hc.mul_left ((coprime_of_same_support C D a hC.1 hD.1
    (sectorPool_supported C hC.1 S a).1 hCD).mp hc)

theorem independent_sector_pools (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (S : Finset (Ideal O)) (F : Ideal O → Ideal O → ℂ) :
    (∑ a∈residualPool C hC (supportedColumns S),∑ b∈residualPool D hD (supportedColumns S),
      if IsCoprime C a ∧ IsCoprime C b ∧ IsCoprime a b then F a b else 0)=
    ∑ a : sectorPool C hC S,∑ b : sectorPool D hD S,
      if IsCoprime (a:Ideal O) (b:Ideal O) then F a b else 0 := by
  have he (a : Ideal O) :
      (∑ b : sectorPool D hD S,if IsCoprime a (b:Ideal O) then F a b else 0)=
      ∑ b∈sectorPool D hD S,if IsCoprime a b then F a b else 0 :=
    Finset.sum_coe_sort (sectorPool D hD S) (fun b : Ideal O => if IsCoprime a b then F a b else 0)
  simp_rw [he]
  rw [Finset.sum_coe_sort (sectorPool C hC S)
    (fun a => ∑ b∈sectorPool D hD S,if IsCoprime a b then F a b else 0)]
  simp only [sectorPool,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hCa : IsCoprime C a
  · simp only [hCa,ite_true,true_and]
    apply Finset.sum_congr rfl
    intro b hb
    have hcb := coprime_of_same_support C D b hC hD
      (residualPool_supported D hD S ⟨b,hb⟩).1 hCD
    by_cases hDb : IsCoprime D b <;> simp [hcb,hDb]
  · simp only [hCa,ite_false,false_and,Finset.sum_const_zero]

end SevenEighths.CenteredMomentSecondSectorColumns

end

end OAI

end Source456

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondCanonical.lean; sha256: dcca9fd743b32b11644a9027579b3f502a553bf98985ab117b61084e9c3b945e -/
section Source457
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonical
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstCanonicalFamily
open CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentSupportedCorrelation
open CenteredMomentSourceRow UniqueFactorizationMonoid CenteredMomentSupport CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

def commonPrime (C D : Ideal O) (P : CommonIndex C D) : O := primaryGenerator P.val

theorem commonPrime_supported_ideal (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    Supported P.val :=
  supported_of_dvd P.val C hC
    (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1))

theorem commonPrime_span (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    Ideal.span {commonPrime C D P}=P.val :=
  primary_span_supported P.val (commonPrime_supported_ideal C D hC P)

theorem commonPrime_supported (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    Supported (Ideal.span {commonPrime C D P}) := by
  rw [commonPrime_span C D hC P]
  exact commonPrime_supported_ideal C D hC P

theorem commonPrime_coprime (C D : Ideal O) (hC : Supported C) :
    Pairwise (Function.onFun IsCoprime (commonPrime C D)) := by
  intro P Q hPQ
  change IsCoprime (commonPrime C D P) (commonPrime C D Q)
  rw [←Ideal.isCoprime_span_singleton_iff,commonPrime_span C D hC P,commonPrime_span C D hC Q]
  exact Ideal.isCoprime_of_isMaximal (fun he=>hPQ (Subtype.ext he))

theorem commonPart_eq_left (C D : Ideal O) (hC : C≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) : commonPart C D=C := by
  have hs : commonSupport C D=commonSupport C C := by
    change CompletedGauss.primeSupport C∩CompletedGauss.primeSupport D=
      CompletedGauss.primeSupport C∩CompletedGauss.primeSupport C
    rw [hCD]
  calc
    commonPart C D=commonPart C C := by unfold commonPart;rw [hs]
    _=C := commonPart_self C hC

theorem left_ideal_product (C D : Ideal O) (hC : Supported C)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    (∏ P : CommonIndex C D,Ideal.span {commonPrime C D P}^leftExponent C D P)=C := by
  simp_rw [commonPrime_span C D hC]
  rw [←commonPart_left_product,commonPart_eq_left C D hC.1 hCD]

theorem right_ideal_product (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    (∏ P : CommonIndex C D,Ideal.span {commonPrime C D P}^rightExponent C D P)=D := by
  simp_rw [commonPrime_span C D hC]
  rw [←commonPart_right_product,commonPart_eq_left D C hD.1 hCD.symm]

theorem left_generator_product (C D : Ideal O) (hC : Supported C)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    (∏ P : CommonIndex C D,commonPrime C D P^leftExponent C D P)=primaryGenerator C := by
  have he := congrArg primaryGeneratorHom (left_ideal_product C D hC hCD)
  simp_rw [commonPrime_span C D hC] at he
  simpa only [map_prod,map_pow,primaryGeneratorHom,MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk,commonPrime] using he

theorem right_generator_product (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    (∏ P : CommonIndex C D,commonPrime C D P^rightExponent C D P)=primaryGenerator D := by
  have he := congrArg primaryGeneratorHom (right_ideal_product C D hC hD hCD)
  simp_rw [commonPrime_span C D hC] at he
  simpa only [map_prod,map_pow,primaryGeneratorHom,MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk,commonPrime] using he

def commonFrequencyGenerator (C D : Ideal O) : O :=
  ∏ P : CommonIndex C D,commonPrime C D P^min (leftExponent C D P) (rightExponent C D P)

theorem actual_ideal_secondSaving_lower (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (w : O) (Z : ℝ) (hZ : 1<Z)
    (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0) :
    (Real.logb Z (Ideal.absNorm C:ℝ)+Real.logb Z (Ideal.absNorm D:ℝ))/3≤
      secondSaving (commonPrime C D) (leftExponent C D) (rightExponent C D) w Z := by
  let (P : CommonIndex C D) : (Ideal.span {commonPrime C D P}).IsMaximal := by
    rw [commonPrime_span C D hC P]
    infer_instance
  have hg (P : CommonIndex C D) : goodLambda∉Ideal.span {commonPrime C D P} := by
    rw [commonPrime_span C D hC P]
    exact common_good C D hC P
  have hc (P : CommonIndex C D) : ringChar (O⧸Ideal.span {commonPrime C D P})≠2 := by
    rw [commonPrime_span C D hC P]
    exact common_odd C D hC P
  have hn : actualCorrelation (∏ P : CommonIndex C D,commonPrime C D P^leftExponent C D P)
      (∏ P : CommonIndex C D,commonPrime C D P^rightExponent C D P)
      (supported_product _ (fun P=>supported_power _ (commonPrime_supported C D hC P) _))
      (supported_product _ (fun P=>supported_power _ (commonPrime_supported C D hC P) _))
      (commonFrequencyGenerator C D*w)≠0 := by
    simpa only [left_generator_product C D hC hCD,right_generator_product C D hC hD hCD,
      idealCorrelation] using hne
  have hh := actual_secondSaving_lower (commonPrime C D) (commonPrime_supported C D hC) hg hc
    (commonPrime_coprime C D hC) (leftExponent C D) (rightExponent C D)
    (leftExponent_pos C D) (rightExponent_pos C D) w Z hZ hn
  rw [left_ideal_product C D hC hCD,right_ideal_product C D hC hD hCD] at hh
  exact hh

end SevenEighths.CenteredMomentSecondCanonical

end

end OAI

end Source457

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstCanonicalAllowance.lean; sha256: 7fb47453ca2723661dd200119af51b2d9d969c35043f116650b23a6b58598e29 -/
section Source458
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentFirstCanonicalAllowance
open ActualEisensteinCubic CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentActive CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentSecondCanonical CenteredMomentFirstCanonicalFamily
open CenteredMomentRankinRadical CenteredMomentCommonAllowance
local notation "O" => ActualEisensteinCubic.O

theorem activeConductor_span_product (I J : Ideal O) :
    Ideal.span {activeConductor I J} =
      ∏ P ∈ activeSupport (Finset.univ : Finset (CommonIndex I J))
        (leftExponent I J) (rightExponent I J), P.val := by
  rw [activeConductor, span_finitePrimeModulus]
  exact Finset.prod_coe_sort (s := ActiveIndex I J)
    (f := fun P : CommonIndex I J => P.val)

theorem active_generator_ideal_product (I J : Ideal O) (hI : Supported I) :
    (∏ P ∈ activeSupport (Finset.univ : Finset (CommonIndex I J))
      (leftExponent I J) (rightExponent I J), Ideal.span {commonPrime I J P}) =
      Ideal.span {activeConductor I J} := by
  simp_rw [commonPrime_span I J hI]
  exact (activeConductor_span_product I J).symm

theorem common_ideal_product (I J : Ideal O) :
    (∏ P : CommonIndex I J, P.val) = commonRadical I J := by
  exact Finset.prod_coe_sort (s := commonSupport I J) (f := fun P : Ideal O => P)

theorem common_generator_ideal_product (I J : Ideal O) (hI : Supported I) :
    (∏ P : CommonIndex I J, Ideal.span {commonPrime I J P}) = commonRadical I J := by
  simp_rw [commonPrime_span I J hI]
  exact common_ideal_product I J

theorem commonRadical_active_principal (I J : Ideal O) :
    commonRadical I J = Ideal.span {activeConductor I J} *
      ∏ P ∈ principalSupport (Finset.univ : Finset (CommonIndex I J))
        (leftExponent I J) (rightExponent I J), P.val := by
  rw [← common_ideal_product, activeConductor_span_product]
  simpa only [CenteredMomentActive.activeSupport, CenteredMomentActive.principalSupport, not_not] using
    (Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun P : CommonIndex I J => netExponent (leftExponent I J P) (rightExponent I J P) ≠ 0)
    (fun P => P.val)).symm

theorem actual_canonical_common_support_allowance
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (Z : ℝ) (hZ : 1 < Z) :
    let c := Real.logb Z (C.absNorm : ℝ)
    let d := Real.logb Z (D.absNorm : ℝ)
    let p := Real.logb Z ((commonRadical C D).absNorm : ℝ)
    let r := Real.logb Z ((Ideal.span {activeConductor C D}).absNorm : ℝ)
    max (3*c-5*d-r) 0/6 + max (3*d-5*c-r) 0/6 ≤ c+d-2*p-r := by
  have h := actual_common_support_allowance (commonPrime C D)
    (commonPrime_supported C D hC) (leftExponent C D) (rightExponent C D)
    (leftExponent_pos C D) (rightExponent_pos C D) Z hZ
  dsimp only at h ⊢
  rw [left_ideal_product C D hC hCD, right_ideal_product C D hC hD hCD,
    common_generator_ideal_product C D hC, active_generator_ideal_product C D hC] at h
  exact h

theorem activeConductor_span_filter (I J : Ideal O) :
    Ideal.span {activeConductor I J} =
      ∏ P ∈ (commonSupport I J).filter (fun P =>
        netExponent (CenteredExceptionalCount.valuation I P)
          (CenteredExceptionalCount.valuation J P) ≠ 0), P := by
  rw [activeConductor_span_product]
  simp only [CenteredMomentActive.activeSupport, Finset.prod_filter]
  exact Finset.prod_coe_sort (s := commonSupport I J)
    (f := fun P : Ideal O => if netExponent (CenteredExceptionalCount.valuation I P)
      (CenteredExceptionalCount.valuation J P) ≠ 0 then P else 1)

theorem extracted_activeConductor_span (I J : Ideal O) :
    Ideal.span {activeConductor (commonPart I J) (commonPart J I)} =
      Ideal.span {activeConductor I J} := by
  have hs : commonSupport (commonPart I J) (commonPart J I) = commonSupport I J := by
    unfold commonSupport
    rw [commonPart_support, commonPart_support, commonSupport_comm J I, Finset.inter_self]
    rfl
  rw [activeConductor_span_filter, activeConductor_span_filter, hs]
  apply Finset.prod_congr
  · apply Finset.filter_congr
    intro P hP
    rw [commonPart_valuation, commonPart_valuation, commonSupport_comm J I,
      ite_eq_left hP, ite_eq_left hP]
  · intro P _
    rfl

theorem actual_extracted_common_support_allowance
    (I J : Ideal O) (hI : Supported I) (hJ : Supported J) (Z : ℝ) (hZ : 1 < Z) :
    let c := Real.logb Z ((commonPart I J).absNorm : ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm : ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm : ℝ)
    let r := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm : ℝ)
    max (3*c-5*d-r) 0/6 + max (3*d-5*c-r) 0/6 ≤ c+d-2*p-r := by
  have h := actual_canonical_common_support_allowance
    (commonPart I J) (commonPart J I) (commonPart_supported I J hI)
    (commonPart_supported J I hJ) (commonParts_equal_support I J) Z hZ
  dsimp only at h ⊢
  rw [extracted_commonRadical, extracted_activeConductor_span] at h
  exact h

end SevenEighths.CenteredMomentFirstCanonicalAllowance

end

end OAI

end Source458

/- Original source: OAI/NumberTheory/DirichletL/Moments/DescentLedger.lean; sha256: 7970798e5301a73afce63b2733d2a8bef850cb2c702378e3415b42e98bbcbfcf -/
section Source459
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDescentLedger
open CanonicalQuadraticSieve CenteredMomentSecondLedger CenteredMomentPartitionNorm
local notation "O" => ActualEisensteinCubic.O

def firstSaving (c D₀ w q wo B g ell : ℝ) : ℝ :=
  c/6+5*D₀/6+w/3+q/6+wo+B-5*g/6+ell

theorem firstSaving_lower (c d D₀ w q R wo B g ell σ δ : ℝ)
    (hc : 0 ≤ c) (hw : 0 ≤ w) (hq : 0 ≤ q) (hwo : 0 ≤ wo)
    (hB : 0 ≤ B) (hσ : 0 ≤ σ) (hδ : 0 ≤ δ)
    (hR : R ≤ q) (hBcost : max (3*c-5*d-R) 0/6 ≤ B)
    (hD : d-δ ≤ D₀) (hg : g ≤ max (D₀-c-2*w+wo) 0+2*σ)
    (hell : 0 ≤ ell) (hwσ : w ≤ 7*σ/3) :
    2*(c+w)/3-3*σ-5*δ/6 ≤ firstSaving c D₀ w q wo B g ell := by
  have hraw : 3*c-5*d-R ≤ 6*B := by
    have hm := le_max_left (3*c-5*d-R) 0
    linarith
  have hmax : max (3*c-5*D₀) 0/6-5*δ/6 ≤ B+q/6 := by
    apply (max_le_iff.mpr ⟨?_,?_⟩ : max (3*c-5*D₀) 0 ≤ 6*(B+q/6)+5*δ) |> fun h => by linarith
    · linarith
    · positivity
  unfold firstSaving
  by_cases hJ : 0 ≤ D₀-c-2*w+wo
  · rw [max_eq_left hJ] at hg
    linarith
  · rw [max_eq_right (le_of_not_ge hJ)] at hg
    have hm := le_max_left (3*c-5*D₀) 0
    linarith

section ActualSecond
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem common_log_ge_unit (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (U : Finset ι) (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.absNorm (unitIdeal p U) : ℝ) ≤
      Real.logb Z (Ideal.absNorm (commonIdeal p c d) : ℝ) := by
  rw [unitIdeal,log_norm_radical p hp,commonIdeal,log_norm_power_product p hp]
  calc
    _ ≤ ∑ i, Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
      intro i hi hni
      apply Real.logb_nonneg hZ
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      have hn : 0 ≤ Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) :=
        Real.logb_nonneg hZ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1))
      have hm : (1:ℝ) ≤ (min (c i) (d i) : ℕ) := by exact_mod_cast le_min (hc i) (hd i)
      nlinarith

omit [DecidableEq ι] in
theorem half_product_log_ge_radical (p : ι → O)
    (hp : ∀ i, Supported (Ideal.span {p i}))
    (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}) : ℝ) ≤
      (Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^c i) : ℝ)+
       Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^d i) : ℝ))/2 := by
  rw [log_norm_radical p hp,log_norm_power_product p hp,log_norm_power_product p hp,
    ← Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  have hn : 0 ≤ Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) :=
    Real.logb_nonneg hZ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1))
  have hcr : (1:ℝ) ≤ c i := by exact_mod_cast hc i
  have hdr : (1:ℝ) ≤ d i := by exact_mod_cast hd i
  nlinarith
end ActualSecond

theorem declared_width_drop (M J g g₂ t₂ σ m' q' δ : ℝ)
    (hwidth : m'+q'=M+J-g-g₂+t₂) (hg : J+σ ≤ g) (hcommon : t₂ ≤ g₂)
    (hnonempty : 0 ≤ m'+δ) :
    max 0 (m'+δ)+q' ≤ M-σ+δ := by
  rw [max_eq_right hnonempty]
  linarith

theorem child_allowance_lower (b₂ p₂ w B ell : ℝ)
    (hbp : p₂ ≤ b₂) (hB : 0 ≤ B) :
    w+ell ≤ b₂-p₂+w+B+ell := by linarith

theorem exceptional_excess_identity
    (A m q c d R E K w wo B g ell b₂ p₂ g₂ t₂ V f : ℝ) :
    let a₀ := A-c-w
    let K₀ := 2*A-c-d+R+E-m
    let m' := 2*a₀-K-g-g₂-V
    let q' := q+R+E+wo+t₂+V
    (m'-f)/6+a₀-b₂-(m'+q'+(b₂-p₂+w+B+ell)) =
      A-5*(m+q)/6-firstSaving c (d+K₀-K) w (q+R+E) wo B g ell -
        (2*b₂-5*g₂/6-p₂+t₂+V/6+f/6) := by
  dsimp only [firstSaving]
  ring

theorem inner_allowance_identity
    (a₀ q wo w B s₀ K g ell p₂ g₂ t₂ b₂ V : ℝ) :
    (a₀+q+wo+w+B-s₀)-(K+g-ell-a₀+p₂-s₀+g₂-t₂-b₂) =
      (2*a₀-K-g-g₂-V)+(q+wo+t₂+V)+(b₂-p₂+w+B+ell) := by ring

theorem exceptional_excess_bound
    (A M c w b₂ F₁ F₂ σ δ : ℝ)
    (hF₁ : 2*(c+w)/3-3*σ-5*δ/6 ≤ F₁)
    (hF₂ : 2*b₂/3 ≤ F₂) :
    A-5*M/6-F₁-F₂ ≤ A-5*M/6-2*(c+w+b₂)/3+3*σ+5*δ/6 := by linarith

theorem uncentered_exceptional_bound
    (A M c w b₂ F₁ F₂ σ δ : ℝ)
    (hA : A ≤ 5*M/6) (hc : 0 ≤ c) (hw : 0 ≤ w) (hb : 0 ≤ b₂)
    (hF₁ : 2*(c+w)/3-3*σ-5*δ/6 ≤ F₁)
    (hF₂ : 2*b₂/3 ≤ F₂) :
    A-5*M/6-F₁-F₂ ≤ 3*σ+5*δ/6 := by
  have hh := exceptional_excess_bound A M c w b₂ F₁ F₂ σ δ hF₁ hF₂
  linarith

end SevenEighths.CenteredMomentDescentLedger

end

end OAI

end Source459

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstExtractedLedger.lean; sha256: dd5d08f90a32062fc05f70e6409b0e3becbce3590518a6966dec669b3fb43749 -/
section Source460
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstExtractedLedger
open CanonicalQuadraticSieve CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentRankinRadical
open CenteredMomentFirstCanonicalAllowance CenteredMomentDescentLedger
local notation "O" => ActualEisensteinCubic.O

theorem actual_extracted_first_saving (I J:Ideal O) (hI:Supported I) (hJ:Supported J)
    (Z:ℝ) (hZ:1<Z):
    let c:=Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d:=Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p:=Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R:=Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let B:=c+d-2*p-R
    ∀D₀ w q wo g ell σ δ:ℝ,0≤w → 0≤q → 0≤wo → 0≤σ → 0≤δ →
      R≤q → d-δ≤D₀ → g≤max (D₀-c-2*w+wo) 0+2*σ → 0≤ell → w≤7*σ/3 →
      2*(c+w)/3-3*σ-5*δ/6≤firstSaving c D₀ w q wo B g ell:=by
  dsimp only
  intro D₀ w q wo g ell σ δ hw hq hwo hσ hδ hR hD hg hell hwσ
  have ha:=actual_extracted_common_support_allowance I J hI hJ Z hZ
  dsimp only at ha
  have hn:(1:ℝ)≤((commonPart I J).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (commonPart_supported I J hI).1)
  have hc:0≤Real.logb Z ((commonPart I J).absNorm:ℝ):=Real.logb_nonneg hZ hn
  have hsecond:0≤max (3*Real.logb Z ((commonPart J I).absNorm:ℝ)-
      5*Real.logb Z ((commonPart I J).absNorm:ℝ)-
      Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6:=by positivity
  have hfirst:0≤max (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
      5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
      Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6:=by positivity
  exact firstSaving_lower _ _ D₀ w q _ wo _ g ell σ δ hc hw hq hwo
    (by linarith) hσ hδ hR (by linarith) hD hg hell hwσ

end SevenEighths.CenteredMomentFirstExtractedLedger

end

end OAI

end Source460

/- Original source: OAI/NumberTheory/DirichletL/Moments/Scale.lean; sha256: 2aa15a33c9a28a32f1513097b165546faee8c7c2a6aa2a6b0bba377e4ca976d4 -/
section Source461
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentScale
open CenteredMomentSmooth EisensteinSchwartzPoisson

theorem logarithmic_kernel_argument (K H A B K₀ H₀ A₀ B₀ : ℝ)
    (hK : 0 < K) (hH : 0 < H) (hA : 0 < A) (hB : 0 < B)
    (hK₀ : 0 < K₀) (hH₀ : 0 < H₀) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) :
    (K₀ * H₀ / (A₀ * B₀)) *
      Real.exp (Real.log (K / K₀) + Real.log (H / H₀) -
        Real.log (A / A₀) - Real.log (B / B₀)) = K * H / (A * B) := by
  rw [Real.exp_sub, Real.exp_sub, Real.exp_add,
    Real.exp_log (div_pos hK hK₀), Real.exp_log (div_pos hH hH₀),
    Real.exp_log (div_pos hA hA₀), Real.exp_log (div_pos hB hB₀)]
  field_simp

theorem rootWindow_log_ratio (V : ℝ → ℂ) (A A₀ : ℝ) (hA : 0 < A) (hA₀ : 0 < A₀) :
    rootWindow V (Real.log (A / A₀)) =
      (Real.sqrt A₀ : ℂ) * V (Real.log (A / A₀)) / (Real.sqrt A : ℂ) := by
  rw [rootWindow, Real.exp_log (div_pos hA hA₀), Real.sqrt_div hA.le, Complex.ofReal_div]
  field_simp

theorem wholeKernel_actual (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (K H A B K₀ H₀ A₀ B₀ : ℝ)
    (hK : 0 < K) (hH : 0 < H) (hA : 0 < A) (hB : 0 < B)
    (hK₀ : 0 < K₀) (hH₀ : 0 < H₀) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) :
    wholeKernel W V (K₀ * H₀ / (A₀ * B₀))
      (Real.log (K / K₀)) (Real.log (H / H₀))
      (Real.log (A / A₀)) (Real.log (B / B₀)) =
      (((Real.sqrt A₀ : ℂ) * (Real.sqrt B₀ : ℂ)) /
        ((Real.sqrt A : ℂ) * (Real.sqrt B : ℂ))) *
      (V 0 (Real.log (K / K₀)) * V 1 (Real.log (H / H₀)) *
        V 2 (Real.log (A / A₀)) * V 3 (Real.log (B / B₀))) *
      paperRadialFourier W (K * H / (A * B)) := by
  rw [wholeKernel, rootWindow_log_ratio _ A A₀ hA hA₀,
    rootWindow_log_ratio _ B B₀ hB hB₀,
    logarithmic_kernel_argument K H A B K₀ H₀ A₀ B₀ hK hH hA hB hK₀ hH₀ hA₀ hB₀]
  ring

theorem normalized_kernel_actual (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (K H A B K₀ H₀ A₀ B₀ : ℝ)
    (hK : 0 < K) (hH : 0 < H) (hA : 0 < A) (hB : 0 < B)
    (hK₀ : 0 < K₀) (hH₀ : 0 < H₀) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) :
    (K : ℂ) / ((Real.sqrt A : ℂ) * (Real.sqrt B : ℂ)) *
      (V 0 (Real.log (K / K₀)) * V 1 (Real.log (H / H₀)) *
        V 2 (Real.log (A / A₀)) * V 3 (Real.log (B / B₀))) *
      paperRadialFourier W (K * H / (A * B)) =
    (K : ℂ) / ((Real.sqrt A₀ : ℂ) * (Real.sqrt B₀ : ℂ)) *
      wholeKernel W V (K₀ * H₀ / (A₀ * B₀))
        (Real.log (K / K₀)) (Real.log (H / H₀))
        (Real.log (A / A₀)) (Real.log (B / B₀)) := by
  rw [wholeKernel_actual W V K H A B K₀ H₀ A₀ B₀ hK hH hA hB hK₀ hH₀ hA₀ hB₀]
  have ha : (Real.sqrt A₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hA₀).ne'
  have hb : (Real.sqrt B₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hB₀).ne'
  field_simp

end SevenEighths.CenteredMomentScale

end

end OAI

end Source461

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstScale.lean; sha256: dfb796bc931c984c2345a239276d4e12e16eee39fc07256090a5de85f163f192 -/
section Source462
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

def firstNominalScale (I J E : Ideal O) (K X : ℝ) : ℝ :=
  (Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*X^2 /
    (K*(Ideal.absNorm (commonPart I J):ℝ)*(Ideal.absNorm (commonPart J I):ℝ))

theorem norm_pos (I : Ideal O) (hI : I≠0) : 0<(Ideal.absNorm I:ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)

theorem active_norm_pos (I J : Ideal O) :
    0<(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ) := by
  apply norm_pos
  exact Ideal.span_singleton_eq_bot.not.mpr (ActualEisensteinCubic.finitePrimeModulus_ne_zero _)

theorem firstNominalScale_pos (I J E : Ideal O) (hE : E≠0) (K X : ℝ)
    (hK : 0<K) (hX : 0<X) : 0<firstNominalScale I J E K X := by
  unfold firstNominalScale
  exact div_pos (mul_pos (mul_pos (norm_pos E hE) (active_norm_pos I J)) (sq_pos_of_pos hX))
    (mul_pos (mul_pos hK (norm_pos _ (commonPart_ne_zero I J))) (norm_pos _ (commonPart_ne_zero J I)))

theorem first_kernel_ratio (I J E : Ideal O) (hI : I≠0) (hJ : J≠0) (hE : E≠0)
    (K X H : ℝ) (hK : 0<K) (hX : 0<X) :
    K*H/((Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*
      (Ideal.absNorm (residualPart I J):ℝ)*(Ideal.absNorm (residualPart J I):ℝ)) =
      (H/firstNominalScale I J E K X)*(X^2/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))) := by
  have hc := norm_pos _ (commonPart_ne_zero I J)
  have hd := norm_pos _ (commonPart_ne_zero J I)
  have he := norm_pos E hE
  have hr := active_norm_pos I J
  have ha := norm_pos _ (residualPart_ne_zero I J)
  have hb := norm_pos _ (residualPart_ne_zero J I)
  have hi : (Ideal.absNorm I:ℝ)=(Ideal.absNorm (commonPart I J):ℝ)*(Ideal.absNorm (residualPart I J):ℝ) := by
    exact_mod_cast absNorm_reconstruct I J hI
  have hj : (Ideal.absNorm J:ℝ)=(Ideal.absNorm (commonPart J I):ℝ)*(Ideal.absNorm (residualPart J I):ℝ) := by
    exact_mod_cast absNorm_reconstruct J I hJ
  rw [hi,hj]
  unfold firstNominalScale
  field_simp

theorem first_kernel_lower (I J E : Ideal O) (hI : I≠0) (hJ : J≠0) (hE : E≠0)
    (K X H HN : ℝ) (hK : 0<K) (hX : 0<X) (hH : 0≤H)
    (hi : (Ideal.absNorm I:ℝ)≤Real.exp HN*X)
    (hj : (Ideal.absNorm J:ℝ)≤Real.exp HN*X) :
    H/(Real.exp (2*HN)*firstNominalScale I J E K X) ≤
      K*H/((Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*
        (Ideal.absNorm (residualPart I J):ℝ)*(Ideal.absNorm (residualPart J I):ℝ)) := by
  rw [first_kernel_ratio I J E hI hJ hE K X H hK hX]
  have hnI := norm_pos I hI
  have hnJ := norm_pos J hJ
  have hT := firstNominalScale_pos I J E hE K X hK hX
  have hh : (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)≤Real.exp (2*HN)*X^2 := by
    calc
      _ ≤ (Real.exp HN*X)*(Real.exp HN*X) := mul_le_mul hi hj hnJ.le (by positivity)
      _ = _ := by rw [show 2*HN=HN+HN by ring,Real.exp_add];ring
  have hr : 1/Real.exp (2*HN) ≤ X^2/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
    apply (div_le_div_iff₀ (Real.exp_pos _) (mul_pos hnI hnJ)).mpr
    simpa only [one_mul,mul_comm] using hh
  calc
    _ = (H/firstNominalScale I J E K X)*(1/Real.exp (2*HN)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr (div_nonneg hH hT.le)

theorem first_kernel_sector_lower (I J E : Ideal O) (hI : I≠0) (hJ : J≠0) (hE : E≠0)
    (K X H HN Tsec : ℝ) (hK : 0<K) (hX : 0<X) (hH : 0≤H)
    (hi : (Ideal.absNorm I:ℝ)≤Real.exp HN*X)
    (hj : (Ideal.absNorm J:ℝ)≤Real.exp HN*X)
    (hsec : firstNominalScale I J E K X≤Tsec) :
    (Real.exp (-2*HN)/Tsec)*H ≤
      K*H/((Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*
        (Ideal.absNorm (residualPart I J):ℝ)*(Ideal.absNorm (residualPart J I):ℝ)) := by
  have hT := firstNominalScale_pos I J E hE K X hK hX
  calc
    _ = H/(Real.exp (2*HN)*Tsec) := by rw [show -2*HN=-(2*HN) by ring,Real.exp_neg];ring
    _ ≤ H/(Real.exp (2*HN)*firstNominalScale I J E K X) :=
      div_le_div_of_nonneg_left hH (mul_pos (Real.exp_pos _) hT)
        (mul_le_mul_of_nonneg_left hsec (Real.exp_pos _).le)
    _ ≤ _ := first_kernel_lower I J E hI hJ hE K X H HN hK hX hH hi hj

end SevenEighths.CenteredMomentFirstScale

end

end OAI

end Source462

/- Original source: OAI/NumberTheory/DirichletL/Moments/SectorLocalization.lean; sha256: 4ef4f37afa0faa756f212aefab63af497809f145480ed7f5320e8822f5d6cda8 -/
section Source463
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSectorLocalization
open CubicEisenstein ConcreteTraceCRT EisensteinSchwartzPoisson CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

def cutoff (x : ℝ) : ℝ := Real.smoothTransition (2-2*x)

theorem cutoff_one (x : ℝ) (hx : x ≤ 1/2) : cutoff x=1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem cutoff_zero (x : ℝ) (hx : 1 ≤ x) : cutoff x=0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem cutoff_bounds (x : ℝ) : 0 ≤ cutoff x ∧ cutoff x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem cutoff_antitone : Antitone cutoff := by
  intro x y hxy
  exact Real.smoothTransition.monotone (by linarith)

def annulus (x : ℝ) : ℝ := cutoff x-cutoff (2*x)

theorem annulus_zero_low (x : ℝ) (hx : x ≤ 1/4) : annulus x=0 := by
  rw [annulus, cutoff_one x (by linarith),cutoff_one (2*x) (by linarith),sub_self]

theorem annulus_zero_high (x : ℝ) (hx : 1 ≤ x) : annulus x=0 := by
  rw [annulus,cutoff_zero x hx,cutoff_zero (2*x) (by linarith),sub_self]

theorem annulus_bounds (x : ℝ) : 0 ≤ annulus x ∧ annulus x ≤ 1 := by
  by_cases hx : x ≤ 1/4
  · rw [annulus_zero_low x hx]; constructor <;> norm_num
  have hm := cutoff_antitone (show x ≤ 2*x by linarith)
  have h₁ := cutoff_bounds x
  have h₂ := cutoff_bounds (2*x)
  unfold annulus
  constructor <;> linarith

theorem annulus_smooth : ContDiff ℝ ∞ annulus := by
  have hc : ContDiff ℝ ∞ cutoff :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))
  exact hc.sub (hc.comp (contDiff_const.mul contDiff_id))

def dyadicScale (n : ℤ) : ℝ := (2:ℝ)^n

theorem dyadicScale_pos (n : ℤ) : 0 < dyadicScale n := by
  unfold dyadicScale
  positivity

theorem dyadicScale_add (n : ℤ) : dyadicScale (n+1)=2*dyadicScale n := by
  simp only [dyadicScale,zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),zpow_one]
  ring

def dyadicWeight (n : ℤ) (q : ℝ) : ℝ := annulus (q/dyadicScale n)

theorem dyadicWeight_smooth (n : ℤ) : ContDiff ℝ ∞ (dyadicWeight n) :=
  annulus_smooth.comp (contDiff_id.div_const _)

theorem dyadicWeight_bounds (n : ℤ) (q : ℝ) :
    0 ≤ dyadicWeight n q ∧ dyadicWeight n q ≤ 1 := annulus_bounds _

theorem dyadicWeight_zero_low (n : ℤ) (q : ℝ) (hq : q ≤ dyadicScale n/4) :
    dyadicWeight n q=0 := by
  apply annulus_zero_low
  apply (div_le_iff₀ (dyadicScale_pos n)).mpr
  linarith

theorem dyadicWeight_zero_high (n : ℤ) (q : ℝ) (hq : dyadicScale n ≤ q) :
    dyadicWeight n q=0 := by
  apply annulus_zero_high
  exact (le_div_iff₀ (dyadicScale_pos n)).mpr (by simpa using hq)

theorem dyadicWeight_support (n : ℤ) :
    Function.support (dyadicWeight n) ⊆ Set.Ioo (dyadicScale n/4) (dyadicScale n) := by
  intro q hq
  constructor
  · exact lt_of_not_ge (fun h => hq (dyadicWeight_zero_low n q h))
  · exact lt_of_not_ge (fun h => hq (dyadicWeight_zero_high n q h))

theorem dyadicWeight_tsupport (n : ℤ) :
    tsupport (dyadicWeight n) ⊆ Set.Icc (dyadicScale n/4) (dyadicScale n) :=
  closure_minimal (fun _ h => Set.Ioo_subset_Icc_self (dyadicWeight_support n h)) isClosed_Icc

theorem dyadicWeight_outside_pair (q : ℝ) (k : ℤ)
    (hlo : dyadicScale k ≤ q) (hhi : q < dyadicScale (k+1))
    (n : ℤ) (hn : n ∉ ({k+1,k+2} : Finset ℤ)) : dyadicWeight n q=0 := by
  have hn₁ : n ≠ k+1 := by simpa using fun h => hn (by simp [h])
  have hn₂ : n ≠ k+2 := by simpa using fun h => hn (by simp [h])
  by_cases hnk : n ≤ k
  · exact dyadicWeight_zero_high n q ((zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hnk).trans hlo)
  · have hkn : k+3 ≤ n := by omega
    have hmono : dyadicScale (k+3) ≤ dyadicScale n :=
      zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hkn
    have he : dyadicScale (k+3)=4*dyadicScale (k+1) := by
      rw [show k+3=(k+1)+1+1 by omega,dyadicScale_add,dyadicScale_add]
      ring
    apply dyadicWeight_zero_low
    rw [he] at hmono
    linarith

theorem dyadicWeight_finite (q : ℝ) : (Function.support (fun n => dyadicWeight n q)).Finite := by
  by_cases hq : 0 < q
  · obtain ⟨k,hlo,hhi⟩ := exists_mem_Ico_zpow hq (by norm_num : (1:ℝ) < 2)
    apply (Set.toFinite (({k+1,k+2} : Finset ℤ) : Set ℤ)).subset
    intro n hn
    by_contra hh
    exact hn (dyadicWeight_outside_pair q k hlo hhi n hh)
  · have hz : ∀ n,dyadicWeight n q=0 := fun n =>
      dyadicWeight_zero_low n q ((le_of_not_gt hq).trans (div_nonneg (dyadicScale_pos n).le (by norm_num)))
    simp [hz]

theorem dyadicWeight_summable (q : ℝ) : Summable (fun n => dyadicWeight n q) :=
  summable_of_hasFiniteSupport (dyadicWeight_finite q)

theorem dyadicWeight_partition (q : ℝ) (hq : 0 < q) : ∑' n,dyadicWeight n q=1 := by
  obtain ⟨k,hlo,hhi⟩ := exists_mem_Ico_zpow hq (by norm_num : (1:ℝ) < 2)
  rw [tsum_eq_sum (s := {k+1,k+2}) (dyadicWeight_outside_pair q k hlo hhi)]
  change dyadicScale k ≤ q at hlo
  change q < dyadicScale (k+1) at hhi
  have hk : k+1 ≠ k+2 := by omega
  rw [Finset.sum_pair hk]
  simp only [dyadicWeight,annulus]
  have h₁ : 2*(q/dyadicScale (k+1))=q/dyadicScale k := by
    rw [dyadicScale_add]; field_simp
  have h₂ : 2*(q/dyadicScale (k+2))=q/dyadicScale (k+1) := by
    rw [show k+2=(k+1)+1 by omega,dyadicScale_add]; field_simp
  rw [h₁,h₂,cutoff_zero _ ((le_div_iff₀ (dyadicScale_pos k)).mpr (by simpa using hlo))]
  have hs : q/dyadicScale (k+2) ≤ 1/2 := by
    apply (div_le_iff₀ (dyadicScale_pos (k+2))).mpr
    rw [show k+2=(k+1)+1 by omega,dyadicScale_add]
    linarith
  rw [cutoff_one _ hs]
  ring

def Retained (R : ℝ) (n : ℤ) : Prop :=
  ∃ q : ℝ, 0 < q ∧ q ≤ R ∧ q ∈ tsupport (dyadicWeight n)

def retainedWeight (R q : ℝ) : ℝ := ∑' n : ℤ, if Retained R n then dyadicWeight n q else 0

def discardedWeight (R q : ℝ) : ℝ := ∑' n : ℤ, if Retained R n then 0 else dyadicWeight n q

theorem retained_summable (R q : ℝ) :
    Summable (fun n : ℤ => if Retained R n then dyadicWeight n q else 0) :=
  (dyadicWeight_summable q).indicator {n | Retained R n}

theorem discarded_summable (R q : ℝ) :
    Summable (fun n : ℤ => if Retained R n then 0 else dyadicWeight n q) := by
  have h := (dyadicWeight_summable q).sub (retained_summable R q)
  convert h using 1
  ext n
  split_ifs <;> simp

theorem retained_add_discarded (R q : ℝ) (hq : 0 < q) :
    retainedWeight R q+discardedWeight R q=1 := by
  rw [retainedWeight,discardedWeight,← (retained_summable R q).tsum_add (discarded_summable R q)]
  convert dyadicWeight_partition q hq using 1
  apply tsum_congr
  intro n
  split_ifs <;> simp

theorem dyadicWeight_zero_nonpos (n : ℤ) (q : ℝ) (hq : q ≤ 0) : dyadicWeight n q=0 :=
  dyadicWeight_zero_low n q (hq.trans (div_nonneg (dyadicScale_pos n).le (by norm_num)))

theorem retainedWeight_zero_nonpos (R q : ℝ) (hq : q ≤ 0) : retainedWeight R q=0 := by
  simp [retainedWeight,dyadicWeight_zero_nonpos _ q hq]

theorem discardedWeight_zero_nonpos (R q : ℝ) (hq : q ≤ 0) : discardedWeight R q=0 := by
  simp [discardedWeight,dyadicWeight_zero_nonpos _ q hq]

theorem retainedWeight_nonneg (R q : ℝ) : 0 ≤ retainedWeight R q := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact (dyadicWeight_bounds n q).1
  · exact le_rfl

theorem discardedWeight_nonneg (R q : ℝ) : 0 ≤ discardedWeight R q := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact le_rfl
  · exact (dyadicWeight_bounds n q).1

theorem retainedWeight_bounds (R q : ℝ) : 0 ≤ retainedWeight R q ∧ retainedWeight R q ≤ 1 := by
  refine ⟨retainedWeight_nonneg R q,?_⟩
  by_cases hq : 0 < q
  · have hp := retained_add_discarded R q hq
    have hd := discardedWeight_nonneg R q
    linarith
  · rw [retainedWeight_zero_nonpos R q (le_of_not_gt hq)]; norm_num

theorem discardedWeight_bounds (R q : ℝ) : 0 ≤ discardedWeight R q ∧ discardedWeight R q ≤ 1 := by
  refine ⟨discardedWeight_nonneg R q,?_⟩
  by_cases hq : 0 < q
  · have hp := retained_add_discarded R q hq
    have hd := retainedWeight_nonneg R q
    linarith
  · rw [discardedWeight_zero_nonpos R q (le_of_not_gt hq)]; norm_num

theorem retained_scale_le (R : ℝ) (n : ℤ) (hn : Retained R n) : dyadicScale n ≤ 4*R := by
  obtain ⟨q,hq,hqR,hs⟩ := hn
  have hb := (dyadicWeight_tsupport n hs).1
  linarith

theorem retainedWeight_zero_above (R q : ℝ) (hq : 4*R ≤ q) : retainedWeight R q=0 := by
  unfold retainedWeight
  trans ∑' _n : ℤ, (0:ℝ)
  · apply tsum_congr
    intro n
    split_ifs with hn
    · exact dyadicWeight_zero_high n q ((retained_scale_le R n hn).trans hq)
    · rfl
  · exact tsum_zero

theorem retainedWeight_enclosure (R q : ℝ) (hq : retainedWeight R q ≠ 0) : 0 < q ∧ q ≤ 4*R := by
  constructor
  · exact lt_of_not_ge (fun h => hq (retainedWeight_zero_nonpos R q h))
  · exact le_of_not_gt (fun h => hq (retainedWeight_zero_above R q h.le))

theorem discardedWeight_zero_below (R q : ℝ) (hq : q ≤ R) : discardedWeight R q=0 := by
  by_cases hp : 0 < q
  · unfold discardedWeight
    trans ∑' _n : ℤ, (0:ℝ)
    · apply tsum_congr
      intro n
      split_ifs with hn
      · rfl
      · by_contra hne
        exact hn ⟨q,hp,hq,subset_tsupport _ hne⟩
    · exact tsum_zero
  · exact discardedWeight_zero_nonpos R q (le_of_not_gt hp)

theorem discardedWeight_support (R q : ℝ) (hq : discardedWeight R q ≠ 0) : R < q :=
  lt_of_not_ge (fun h => hq (discardedWeight_zero_below R q h))

theorem retainedWeight_one_below (R q : ℝ) (hq : 0 < q) (hR : q ≤ R) : retainedWeight R q=1 := by
  have h := retained_add_discarded R q hq
  rwa [discardedWeight_zero_below R q hR,add_zero] at h

theorem finite_retained_integral_dyads (R : ℝ) :
    {n : ℤ | Retained R n ∧ ∃ q : ℝ, 1 ≤ q ∧ dyadicWeight n q ≠ 0}.Finite := by
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (4*R) (by norm_num : (1:ℝ) < 2)
  apply (Set.finite_Icc (1:ℤ) (k:ℤ)).subset
  intro n hn
  obtain ⟨hr,q,hq,hne⟩ := hn
  have hu := retained_scale_le R n hr
  have hs := (dyadicWeight_support n hne).2
  constructor
  · have : (2:ℝ)^(0:ℤ) < (2:ℝ)^n := by simpa [dyadicScale] using hq.trans_lt hs
    have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp this
    omega
  · have h : (2:ℝ)^n < (2:ℝ)^(k:ℤ) := by
      simpa only [zpow_natCast,dyadicScale] using hu.trans_lt hk
    have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp h
    omega

theorem annulus_pos (x : ℝ) (hlo : 1/4 < x) (hhi : x < 1) : 0 < annulus x := by
  by_cases hx : x ≤ 1/2
  · rw [annulus,cutoff_one x hx]
    have h := Real.smoothTransition.lt_one_of_lt_one (by linarith : 2-2*(2*x) < 1)
    exact sub_pos.mpr h
  · rw [annulus,cutoff_zero (2*x) (by linarith),sub_zero]
    exact Real.smoothTransition.pos_of_pos (by linarith)

theorem dyadicWeight_support_eq (n : ℤ) :
    Function.support (dyadicWeight n)=Set.Ioo (dyadicScale n/4) (dyadicScale n) := by
  apply Set.Subset.antisymm (dyadicWeight_support n)
  intro q hq
  apply ne_of_gt
  apply annulus_pos
  · apply (lt_div_iff₀ (dyadicScale_pos n)).mpr
    linarith [hq.1]
  · exact (div_lt_one (dyadicScale_pos n)).mpr hq.2

theorem dyadicWeight_tsupport_eq (n : ℤ) :
    tsupport (dyadicWeight n)=Set.Icc (dyadicScale n/4) (dyadicScale n) := by
  rw [tsupport,dyadicWeight_support_eq,closure_Ioo]
  linarith [dyadicScale_pos n]

theorem retained_iff_scale (R : ℝ) (n : ℤ) : Retained R n ↔ dyadicScale n ≤ 4*R := by
  refine ⟨retained_scale_le R n,fun hn => ?_⟩
  refine ⟨dyadicScale n/4,div_pos (dyadicScale_pos n) (by norm_num),by linarith,?_⟩
  rw [dyadicWeight_tsupport_eq]
  exact ⟨le_rfl,by linarith [dyadicScale_pos n]⟩

theorem retained_boundary (n : ℤ) : Retained (dyadicScale n/4) n := by
  rw [retained_iff_scale]
  linarith

def normValue (h : O) : ℝ := Ideal.absNorm (Ideal.span {h})

theorem normValue_eq_embedding (h : O) : normValue h=‖eisEmbedding h‖^2 :=
  (ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span h).symm

theorem normValue_mul (v h : O) : normValue (v*h)=normValue v*normValue h := by
  simp only [normValue,← Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul]

theorem normValue_pos (h : O) (hh : h ≠ 0) : 0 < normValue h := by
  unfold normValue
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hh))

theorem normValue_ge_one (h : O) (hh : h ≠ 0) : 1 ≤ normValue h := by
  unfold normValue
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hh))

theorem retained_pullback (R : ℝ) (v h : O) :
    retainedWeight R (normValue (v*h))=retainedWeight R (normValue v*normValue h) := by
  rw [normValue_mul]

theorem retained_norm_enclosure (R : ℝ) (v h : O) (hv : v ≠ 0)
    (hne : retainedWeight R (normValue (v*h)) ≠ 0) : normValue h ≤ 4*R/normValue v := by
  have hb := (retainedWeight_enclosure R _ hne).2
  rw [normValue_mul] at hb
  apply (le_div_iff₀ (normValue_pos v hv)).mpr
  nlinarith

def frequencyRadius (Tsec Z ξ : ℝ) : ℝ := Tsec*Z^(ξ/2)

def frequencyLoss (Z Csec ξ : ℝ) : ℝ := ξ/2+Real.logb Z (4*Csec)

theorem frequencyLoss_nonneg (Z Csec ξ : ℝ) (hZ : 1 < Z) (hC : 1 ≤ Csec) (hξ : 0 ≤ ξ) :
    0 ≤ frequencyLoss Z Csec ξ := by
  have hlog := Real.logb_nonneg hZ (show 1 ≤ 4*Csec by linarith)
  unfold frequencyLoss
  linarith

theorem source_enclosure_power (Z Csec L ξ Nv : ℝ) (hZ : 1 < Z) (hC : 0 < Csec) (hNv : 0 < Nv) :
    4*(Csec*Z^L)*Z^(ξ/2)/Nv=Z^(L-Real.logb Z Nv+frequencyLoss Z Csec ξ) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  rw [frequencyLoss,show L-Real.logb Z Nv+(ξ/2+Real.logb Z (4*Csec))=
    (L+ξ/2)+Real.logb Z (4*Csec)-Real.logb Z Nv by ring,
    Real.rpow_sub hz,Real.rpow_add hz,Real.rpow_add hz,
    Real.rpow_logb hz (ne_of_gt hZ),Real.rpow_logb hz (ne_of_gt hZ)]
  · ring
  · exact hNv
  · positivity

theorem actual_retained_row_enclosure (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (v h : O) (hv : v ≠ 0)
    (hne : retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) ≠ 0) :
    normValue h ≤ Z^(L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ) := by
  have hb := retained_norm_enclosure (frequencyRadius Tsec Z ξ) v h hv hne
  apply hb.trans
  rw [← source_enclosure_power Z Csec L ξ (normValue v) hZ hC (normValue_pos v hv)]
  apply div_le_div_of_nonneg_right _ (normValue_pos v hv).le
  dsimp only [frequencyRadius]
  nlinarith [mul_le_mul_of_nonneg_right hT (Real.rpow_nonneg (zero_lt_one.trans hZ).le (ξ/2))]

theorem actual_nonempty_width (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (v h : O) (hv : v ≠ 0) (hh : h ≠ 0)
    (hne : retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) ≠ 0) :
    0 ≤ L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ := by
  have he := (normValue_ge_one h hh).trans (actual_retained_row_enclosure Tsec Z Csec L ξ hZ hC hT v h hv hne)
  by_contra hn
  have hh := Real.rpow_lt_one_of_one_lt_of_neg hZ (lt_of_not_ge hn)
  linarith

theorem actual_declared_width_drop (Tsec Z Csec L ξ M J g g₂ t₂ σ q' : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (v h : O) (hv : v ≠ 0) (hh : h ≠ 0)
    (hne : retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) ≠ 0)
    (hwidth : (L-Real.logb Z (normValue v))+q'=M+J-g-g₂+t₂)
    (hg : J+σ ≤ g) (hcommon : t₂ ≤ g₂) :
    max 0 (L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ)+q' ≤
      M-σ+frequencyLoss Z Csec ξ :=
  CenteredMomentDescentLedger.declared_width_drop M J g g₂ t₂ σ _ q' _ hwidth hg hcommon
    (actual_nonempty_width Tsec Z Csec L ξ hZ hC hT v h hv hh hne)

theorem retained_first_dyad_enclosure (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z ξ) n) :
    Real.logb Z (dyadicScale n) ≤ L+frequencyLoss Z Csec ξ := by
  have hb := retained_scale_le _ n hn
  have hp := source_enclosure_power Z Csec L ξ 1 hZ hC (by norm_num)
  simp only [Real.logb_one,sub_zero,div_one] at hp
  have he : dyadicScale n ≤ Z^(L+frequencyLoss Z Csec ξ) := by
    rw [← hp]
    dsimp only [frequencyRadius] at hb
    nlinarith [mul_le_mul_of_nonneg_right hT (Real.rpow_nonneg (zero_lt_one.trans hZ).le (ξ/2))]
  have hl := Real.logb_le_logb_of_le hZ (dyadicScale_pos n) he
  rwa [Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] at hl

def kernelReference (Tsec H : ℝ) : ℝ := Real.exp (-2*H)/Tsec

theorem kernelReference_pos (Tsec H : ℝ) (hT : 0 < Tsec) : 0 < kernelReference Tsec H :=
  div_pos (Real.exp_pos _) hT

theorem frequencyLoss_lt (Z Csec H ξ : ℝ) (hZ : 1 < Z) (hH : 0 ≤ H) (hξ : 0 < ξ)
    (hthreshold : 2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) :
    frequencyLoss Z Csec ξ < ξ := by
  have h := div_nonneg (show 0 ≤ 2*H by linarith) (Real.log_pos hZ).le
  unfold frequencyLoss Real.logb
  linarith

theorem discarded_kernel_argument (Tsec Z Csec H ξ q : ℝ)
    (hT : 0 < Tsec) (hZ : 1 < Z) (hC : 1 ≤ Csec)
    (hthreshold : 2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4)
    (hne : discardedWeight (frequencyRadius Tsec Z ξ) q ≠ 0) :
    Z^(ξ/4) ≤ kernelReference Tsec H*q := by
  have hlog := Real.log_nonneg (show 1 ≤ 4*Csec by linarith)
  have hlogdiv := div_nonneg hlog (Real.log_pos hZ).le
  have he : 2*H < ξ/4*Real.log Z :=
    (div_lt_iff₀ (Real.log_pos hZ)).mp (by linarith : 2*H/Real.log Z < ξ/4)
  have hs : Z^(ξ/4) ≤ Real.exp (-2*H)*Z^(ξ/2) := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hZ),Real.rpow_def_of_pos (zero_lt_one.trans hZ),← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hq := (discardedWeight_support _ q hne).le
  have hm := mul_le_mul_of_nonneg_left hq (kernelReference_pos Tsec H hT).le
  have hid : kernelReference Tsec H*frequencyRadius Tsec Z ξ=Real.exp (-2*H)*Z^(ξ/2) := by
    unfold kernelReference frequencyRadius
    field_simp
  rw [hid] at hm
  exact hs.trans hm

theorem retained_pullback_zero_extension (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (v h : O) (hv : v ≠ 0) :
    retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) =
      if normValue h ≤ Z^(L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ)
      then retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) else 0 := by
  split_ifs with hb
  · rfl
  · by_contra hn
    exact hb (actual_retained_row_enclosure Tsec Z Csec L ξ hZ hC hT v h hv hn)

theorem actual_discarded_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (Tsec Z Csec H ξ K B : ℝ),
      0 < Tsec → 1 < Z → 1 ≤ Csec →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) →
      kernelReference Tsec H ≤ K → 0 ≤ B →
      ∀ c : O → ℂ, (∀ h, ‖c h‖ ≤ B) →
      ‖∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*c h*
        paperRadialFourier W (K*normValue h)‖ ≤
      B*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := CenteredMomentTail.uniform_sector_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W Tsec Z Csec H ξ K B hT hZ hCsec hthreshold hK hB c hc
  let D : Set O := {h | discardedWeight (frequencyRadius Tsec Z ξ) (normValue h) ≠ 0}
  have hb := ht W D (kernelReference Tsec H) (Z^(ξ/4)) B
    (kernelReference_pos Tsec H hT) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hB
    (fun h hh => by
      rw [← normValue_eq_embedding]
      exact discarded_kernel_argument Tsec Z Csec H ξ (normValue h) hT hZ hCsec hthreshold hh)
    K hK c (fun h => (discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ))
    (fun h _ => hc h) (fun h _ => by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (discardedWeight_nonneg _ _)]
      exact (discardedWeight_bounds _ _).2)
  simp_rw [← normValue_eq_embedding] at hb
  have he := tsum_subtype_eq_of_support_subset (f := fun h : O =>
    (discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*c h*paperRadialFourier W (K*normValue h))
    (s := D) (by
      intro h hh
      change discardedWeight (frequencyRadius Tsec Z ξ) (normValue h) ≠ 0
      intro hz
      exact hh (by simp [hz]))
  rwa [he] at hb

theorem actual_discarded_second_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (Tsec Z Csec H ξ K : ℝ),
      0 < Tsec → 1 < Z → 1 ≤ Csec →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) →
      kernelReference Tsec H ≤ K →
      ∀ (u v : O) (hu : CanonicalQuadraticSieve.Supported (Ideal.span {u}))
        (hv : CanonicalQuadraticSieve.Supported (Ideal.span {v})),
      ‖∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        CenteredMomentSupportedCorrelation.actualCorrelation u v hu hv (-h)*
        paperRadialFourier W (K*normValue h)‖ ≤
      (normValue u*normValue v)*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := actual_discarded_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W Tsec Z Csec H ξ K hT hZ hCsec hthreshold hK u v hu hv
  exact ht W Tsec Z Csec H ξ K (normValue u*normValue v) hT hZ hCsec hthreshold hK
    (by unfold normValue; positivity) _ (fun h => CenteredMomentTail.actualCorrelation_norm_le u v hu hv (-h))

theorem actual_discarded_first_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (Tsec Z Csec H ξ K : ℝ),
      0 < Tsec → 1 < Z → 1 ≤ Csec →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) →
      kernelReference Tsec H ≤ K →
      ∀ {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (hinj : Function.Injective P) (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ P i)
        (_hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2) (B : Finset ι) (c d : ι → ℕ)
        (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
        (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ),
      let r := CenteredMomentInitial.activeModulus P B c d
      let χr := CenteredMomentInitial.commonCharacter P hinj hg B c d
      ‖∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        (normalizedResidueGauss r (CenteredMomentInitial.activeModulus_ne_zero P B c d) χr
            (Ideal.Quotient.mk _ h)*
          (normalizedResidueGauss a ha χa (Ideal.Quotient.mk _ h)/
            (Real.sqrt (normValue a):ℂ))*
          star (normalizedResidueGauss b hb χb (Ideal.Quotient.mk _ (-h))/
            (Real.sqrt (normValue b):ℂ)))*paperRadialFourier W (K*normValue h)‖ ≤
      (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := actual_discarded_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W Tsec Z Csec H ξ K hT hZ hCsec hthreshold hK ι P _ hinj hg hchar B c d a b ha hb χa χb
  dsimp only
  simpa only [one_mul] using ht W Tsec Z Csec H ξ K 1 hT hZ hCsec hthreshold hK zero_le_one _ (by
    intro h
    rw [norm_mul,norm_mul,norm_star]
    calc
      _ ≤ (1*1)*1 := mul_le_mul
        (mul_le_mul (CenteredMomentInitial.common_gauss_norm_le_one P hinj hg hchar B c d h)
          (CenteredMomentTail.normalizedResidueGauss_div_root_norm_le_one a ha χa _)
          (norm_nonneg _) zero_le_one)
        (CenteredMomentTail.normalizedResidueGauss_div_root_norm_le_one b hb χb _)
        (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num)

theorem retained_product_ne_zero (R : ℝ) (v h : O)
    (hne : retainedWeight R (normValue (v*h)) ≠ 0) : v ≠ 0 ∧ h ≠ 0 := by
  have hp := (retainedWeight_enclosure R _ hne).1
  constructor <;> intro hz <;> simp [hz,normValue] at hp

theorem actual_nonempty_width_of_weight (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L) (v h : O)
    (hne : retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) ≠ 0) :
    0 ≤ L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ := by
  obtain ⟨hv,hh⟩ := retained_product_ne_zero _ v h hne
  exact actual_nonempty_width Tsec Z Csec L ξ hZ hC hT v h hv hh hne

theorem actual_second_pullback (R : ℝ) (Gc V h : O) :
    retainedWeight R (normValue ((Gc*V)*h))=
      retainedWeight R ((normValue Gc*normValue V)*normValue h) := by
  simp only [normValue_mul]

theorem retained_integral_empty (R : ℝ) (hR : 4*R < 1) (h : O) :
    retainedWeight R (normValue h)=0 := by
  by_contra hn
  have hh : h ≠ 0 := by
    intro hz
    subst h
    exact hn (by simpa [normValue] using retainedWeight_zero_nonpos R 0 le_rfl)
  have hb := (retainedWeight_enclosure R _ hn).2
  linarith [normValue_ge_one h hh]

theorem finite_retained_above (R a : ℝ) (ha : 0 < a) :
    {n : ℤ | Retained R n ∧ ∃ q : ℝ, a ≤ q ∧ dyadicWeight n q ≠ 0}.Finite := by
  obtain ⟨k,hk,_⟩ := exists_mem_Ico_zpow ha (by norm_num : (1:ℝ) < 2)
  obtain ⟨l,hl⟩ := pow_unbounded_of_one_lt (4*R) (by norm_num : (1:ℝ) < 2)
  apply (Set.finite_Icc k (l:ℤ)).subset
  intro n hn
  obtain ⟨hr,q,hq,hne⟩ := hn
  have hu := retained_scale_le R n hr
  have hs := (dyadicWeight_support n hne).2
  constructor
  · have h : (2:ℝ)^k < (2:ℝ)^n := hk.trans_lt (hq.trans_lt hs)
    exact ((zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp h).le
  · have h : (2:ℝ)^n < (2:ℝ)^(l:ℤ) := by
      simpa only [zpow_natCast,dyadicScale] using hu.trans_lt hl
    exact ((zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp h).le

theorem retainedWeight_finite_formula (R a : ℝ) (ha : 0 < a) :
    ∃ S : Finset ℤ, ∀ q : ℝ, a ≤ q →
      retainedWeight R q=∑ n ∈ S, if Retained R n then dyadicWeight n q else 0 := by
  let hs := finite_retained_above R a ha
  refine ⟨hs.toFinset,fun q hq => ?_⟩
  apply tsum_eq_sum
  intro n hn
  split_ifs with hr
  · by_contra hne
    exact hn (hs.mem_toFinset.mpr ⟨hr,q,hq,hne⟩)
  · rfl

theorem retainedWeight_smooth_positive (R q : ℝ) (hq : 0 < q) :
    ContDiffAt ℝ ∞ (retainedWeight R) q := by
  obtain ⟨S,hS⟩ := retainedWeight_finite_formula R (q/2) (by linarith)
  have hc : ContDiff ℝ ∞ (fun x : ℝ => ∑ n ∈ S, if Retained R n then dyadicWeight n x else 0) := by
    apply ContDiff.sum
    intro n hn
    by_cases hr : Retained R n
    · simpa [hr] using dyadicWeight_smooth n
    · simpa [hr] using (contDiff_const : ContDiff ℝ ∞ (fun _x : ℝ => (0:ℝ)))
  apply hc.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show q/2 < q by linarith)] with x hx
  exact hS x hx.le

theorem discardedWeight_smooth_positive (R q : ℝ) (hq : 0 < q) :
    ContDiffAt ℝ ∞ (discardedWeight R) q := by
  have hc : ContDiffAt ℝ ∞ (fun x => (1:ℝ)-retainedWeight R x) q :=
    contDiffAt_const.sub (retainedWeight_smooth_positive R q hq)
  apply hc.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hq] with x hx
  have he := retained_add_discarded R x hx
  linarith

end SevenEighths.CenteredMomentSectorLocalization

end

end OAI

end Source463

/- Original source: OAI/NumberTheory/DirichletL/RayOrthogonality.lean; sha256: 85ff7487c61c123c298ed50f372be88338689a5d9d83ed4827bae30664243eed -/
section Source464
namespace OAI

namespace SevenEighths.RayOrthogonality

open scoped Classical
noncomputable section

section FiniteMonoid
variable {R : Type*} [CommMonoid R] [Finite R]

def characters (H : Subgroup Rˣ) : Subgroup (MulChar R ℂ) :=
  (MulChar.subgroupOrderIsoSubgroupMulChar R ℂ H).ofDual

instance (H : Subgroup Rˣ) : Fintype (characters H) := Fintype.ofFinite _

theorem mem_characters_iff (H : Subgroup Rˣ) (χ : MulChar R ℂ) :
    χ ∈ characters H ↔ ∀ u ∈ H, χ u = 1 :=
  MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff

theorem card_characters (H : Subgroup Rˣ) :
    Fintype.card (characters H) = Nat.card (Rˣ ⧸ H) := by
  rw [← Nat.card_eq_fintype_card]
  exact MulChar.card_subgroupOrderIsoSubgroupMulChar

theorem exists_character_ne_one (H : Subgroup Rˣ) {u : Rˣ} (hu : u ∉ H) :
    ∃ χ : characters H, (χ : MulChar R ℂ) u ≠ 1 := by
  by_contra hn
  apply hu
  have hall : ∀ χ ∈ characters H, χ u = 1 := by
    intro χ hχ
    by_contra h
    exact hn ⟨⟨χ, hχ⟩, h⟩
  have hh := (MulChar.mem_subgroupOrderIsoSubgroupMulChar_symm_iff).mpr hall
  simpa only [characters, OrderDual.toDual_ofDual, OrderIso.symm_apply_apply] using hh

theorem sum_characters_unit (H : Subgroup Rˣ) (u : Rˣ) :
    ∑ χ : characters H, (χ : MulChar R ℂ) u =
      if u ∈ H then (Nat.card (Rˣ ⧸ H) : ℂ) else 0 := by
  by_cases hu : u ∈ H
  · simp only [hu, ite_true]
    calc
      _ = ∑ _χ : characters H, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro χ _
        exact (mem_characters_iff H χ).mp χ.property u hu
      _ = _ := by simp [card_characters]
  · simp only [hu, ite_false]
    obtain ⟨χ, hχ⟩ := exists_character_ne_one H hu
    refine eq_zero_of_mul_eq_self_left hχ ?_
    simp only [Finset.mul_sum, ← MulChar.mul_apply]
    exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' ↦ rfl

def inUnitSubgroup (H : Subgroup Rˣ) (r : R) : Prop :=
  ∃ u : Rˣ, (u : R) = r ∧ u ∈ H

theorem sum_characters (H : Subgroup Rˣ) (r : R) :
    ∑ χ : characters H, (χ : MulChar R ℂ) r =
      if inUnitSubgroup H r then (Nat.card (Rˣ ⧸ H) : ℂ) else 0 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    have hi : inUnitSubgroup H (u : R) ↔ u ∈ H := by
      constructor
      · rintro ⟨v, hv, h⟩
        exact (Units.ext hv) ▸ h
      · exact fun h ↦ ⟨u, rfl, h⟩
    rw [sum_characters_unit, hi]
  · have hn : ¬ inUnitSubgroup H r := by
      rintro ⟨u, rfl, _⟩
      exact hr u.isUnit
    simp only [hn, ite_false]
    exact Finset.sum_eq_zero fun χ _ ↦ MulChar.map_nonunit χ.val hr

theorem ray_card_pos (H : Subgroup Rˣ) : 0 < Nat.card (Rˣ ⧸ H) :=
  Nat.card_pos

theorem average_characters (H : Subgroup Rˣ) (r : R) :
    (∑ χ : characters H, (χ : MulChar R ℂ) r) / (Nat.card (Rˣ ⧸ H) : ℂ) =
      if inUnitSubgroup H r then 1 else 0 := by
  rw [sum_characters]
  have hn : (Nat.card (Rˣ ⧸ H) : ℂ) ≠ 0 := by
    exact_mod_cast (ray_card_pos H).ne'
  split_ifs <;> simp [hn]

end FiniteMonoid

section Residues
variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]

def globalUnits : Subgroup (A ⧸ M)ˣ :=
  (Units.map (Ideal.Quotient.mk M).toMonoidHom).range

abbrev rayCharacters := characters (globalUnits M)

theorem mem_rayCharacters_iff (χ : MulChar (A ⧸ M) ℂ) :
    χ ∈ rayCharacters M ↔ IdealCharacter.UnitInvariant M χ := by
  rw [mem_characters_iff]
  constructor
  · intro h u
    exact h _ ⟨u, rfl⟩
  · intro h u hu
    obtain ⟨v, rfl⟩ := hu
    exact h v

def principalResidue (r : A ⧸ M) : Prop :=
  ∃ u : Aˣ, Ideal.Quotient.mk M u = r

omit [Finite (A ⧸ M)] in
theorem inUnitSubgroup_globalUnits_iff (r : A ⧸ M) :
    inUnitSubgroup (globalUnits M) r ↔ principalResidue M r := by
  constructor
  · rintro ⟨u, hur, v, hv⟩
    exact ⟨v, (congrArg Units.val hv).trans hur⟩
  · rintro ⟨u, hu⟩
    exact ⟨Units.map (Ideal.Quotient.mk M).toMonoidHom u, hu, ⟨u, rfl⟩⟩

abbrev rayCard : ℕ := Nat.card ((A ⧸ M)ˣ ⧸ globalUnits M)

theorem rayCard_pos : 0 < rayCard M := ray_card_pos _

theorem sum_rayCharacters (r : A ⧸ M) :
    ∑ χ : rayCharacters M, (χ : MulChar (A ⧸ M) ℂ) r =
      if principalResidue M r then (rayCard M : ℂ) else 0 := by
  rw [sum_characters, inUnitSubgroup_globalUnits_iff]

theorem average_rayCharacters (r : A ⧸ M) :
    (∑ χ : rayCharacters M, (χ : MulChar (A ⧸ M) ℂ) r) / (rayCard M : ℂ) =
      if principalResidue M r then 1 else 0 := by
  rw [average_characters, inUnitSubgroup_globalUnits_iff]

section PrincipalIdeals
variable [IsDomain A] [IsPrincipalIdealRing A]

def idealCharacter (χ : rayCharacters M) : Ideal A →*₀ ℂ :=
  IdealCharacter.ofResidue M χ ((mem_rayCharacters_iff M χ).mp χ.property)

def principalIdeals : Set (Ideal A) :=
  {I | I ≠ ⊥ ∧ ∃ a : A, Ideal.span ({a} : Set A) = I ∧
    principalResidue M (Ideal.Quotient.mk M a)}

omit [Finite (A ⧸ M)] in
theorem principalIdeals_iff_generator {I : Ideal A} (hI : I ≠ ⊥) :
    I ∈ principalIdeals M ↔
      principalResidue M (Ideal.Quotient.mk M (Submodule.IsPrincipal.generator I)) := by
  constructor
  · rintro ⟨_, a, ha, u, hu⟩
    have hga : Associated (Submodule.IsPrincipal.generator I) a := by
      rw [← ha]
      exact Submodule.IsPrincipal.associated_generator_span_self a
    obtain ⟨v, hv⟩ := hga
    refine ⟨u * v⁻¹, ?_⟩
    have hq := congrArg (Ideal.Quotient.mk M) hv
    simp only [map_mul] at hq
    simp only [Units.val_mul, map_mul]
    rw [hu, ← hq]
    rw [mul_assoc, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, mul_one]
  · intro h
    exact ⟨hI, _, Ideal.span_singleton_generator I, h⟩

omit [Finite (A ⧸ M)] [IsPrincipalIdealRing A] in

theorem principalIdeals_iff_congruent_one (I : Ideal A) :
    I ∈ principalIdeals M ↔ ∃ a : A, a ≠ 0 ∧
      Ideal.span ({a} : Set A) = I ∧ Ideal.Quotient.mk M a = 1 := by
  constructor
  · rintro ⟨hI, a, ha, u, hu⟩
    refine ⟨a * (u⁻¹ : Aˣ), ?_, ?_, ?_⟩
    · apply mul_ne_zero
      · exact fun h ↦ hI (ha ▸ (Ideal.span_singleton_eq_bot.mpr h))
      · exact Units.ne_zero _
    · rw [Ideal.span_singleton_mul_right_unit (u⁻¹).isUnit, ha]
    · rw [map_mul, ← hu, ← map_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, map_one]
  · rintro ⟨a, ha, hI, hq⟩
    refine ⟨?_, a, hI, 1, ?_⟩
    · exact fun h ↦ ha (Ideal.span_singleton_eq_bot.mp (hI.trans h))
    · simpa only [Units.val_one, map_one] using hq.symm

theorem norm_idealCharacter_le_one (χ : rayCharacters M) (I : Ideal A) :
    ‖idealCharacter M χ I‖ ≤ 1 := IdealCharacter.norm_ofResidue_le_one M χ _ I

theorem idealCharacter_one (I : Ideal A) :
    idealCharacter M 1 I =
      if I = ⊥ then 0 else if IsCoprime I M then 1 else 0 :=
  IdealCharacter.ofResidue_one M I

theorem sum_idealCharacters (I : Ideal A) :
    ∑ χ : rayCharacters M, idealCharacter M χ I =
      if I ∈ principalIdeals M then (rayCard M : ℂ) else 0 := by
  by_cases hI : I = ⊥
  · subst I
    simp [idealCharacter, principalIdeals]
  · have heq (χ : rayCharacters M) : idealCharacter M χ I =
        (χ : MulChar (A ⧸ M) ℂ) (Ideal.Quotient.mk M (Submodule.IsPrincipal.generator I)) := by
      exact IdealCharacter.ofResidue_of_generator M χ _ hI (Ideal.span_singleton_generator I)
    simp only [heq, sum_rayCharacters, principalIdeals_iff_generator M hI]

theorem average_idealCharacters (I : Ideal A) :
    (∑ χ : rayCharacters M, idealCharacter M χ I) / (rayCard M : ℂ) =
      if I ∈ principalIdeals M then 1 else 0 := by
  rw [sum_idealCharacters]
  have hn : (rayCard M : ℂ) ≠ 0 := by exact_mod_cast (rayCard_pos M).ne'
  split_ifs <;> simp [hn]

end PrincipalIdeals
end Residues

end
end SevenEighths.RayOrthogonality

end OAI

end Source464

/- Original source: OAI/NumberTheory/DirichletL/Hecke/Boundary.lean; sha256: 10cf42c76993a667b631241e70e3105681331d83a466beb9cdb069392d623fc6 -/
section Source465
namespace OAI

namespace SevenEighths.HeckeBoundary

open ActualEisensteinCubic Complex
open SevenEighths.IdealEuler SevenEighths.IdealCharacter
open SmoothMobiusCorrection (PrimeIdeal)
open Asymptotics Filter
open scoped BigOperators Classical Topology

noncomputable section

theorem re_log_comb_nonneg {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re +
      (-log (1 - a * z ^ 2)).re := by
  have hac₀ : ‖(a : ℂ)‖ < 1 := by
    simp only [Complex.norm_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3).add
    ((hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4) |>.add
    (hasSum_re <| hasSum_taylorSeries_neg_log hac₂) |>.tsum_eq]
  refine tsum_nonneg fun n ↦ ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul,
    sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    rw [← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, ← sq_norm_sub_sq_re, norm_pow, hz]
    convert! (show 0 ≤ 2 * a ^ n * ((z ^ n).re + 1) ^ 2 by positivity) using 1
    ring

theorem re_log_cpow_comb_nonneg {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 1 < x)
    (y : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - (n : ℂ) ^ (-x : ℂ))).re +
      4 * (-log (1 - z * (n : ℂ) ^ (-(x + I * y)))).re +
      (-log (1 - z ^ 2 * (n : ℂ) ^ (-(x + 2 * I * y)))).re := by
  have hn' : (n : ℝ) ^ (-x) < 1 := by
    rw [Real.rpow_neg (Nat.cast_nonneg n), inv_lt_one_iff₀]
    exact .inr <| Real.one_lt_rpow (mod_cast one_lt_two.trans_le hn) <| zero_lt_one.trans hx
  have hz' : ‖z * (n : ℂ) ^ (-(I * y))‖ = 1 := by
    rw [norm_mul, hz, ← ofReal_natCast,
      norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast (by omega : (0 : ℕ) < n))]
    simp
  convert! re_log_comb_nonneg (by positivity) hn' hz' using 6
  · simp only [ofReal_cpow n.cast_nonneg (-x), ofReal_natCast, ofReal_neg]
  · congr 2
    rw [neg_add, cpow_add _ _ <| mod_cast by omega, ← ofReal_neg,
      ofReal_cpow n.cast_nonneg (-x), ofReal_natCast, mul_left_comm]
  · rw [neg_add, cpow_add _ _ <| mod_cast by omega, ← ofReal_neg,
      ofReal_cpow n.cast_nonneg (-x), ofReal_natCast,
      show -(2 * I * y) = (2 : ℕ) * -(I * y) by ring, cpow_nat_mul, mul_pow,
      mul_left_comm]

theorem summable_neg_log_euler (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun P : PrimeIdeal => -log (1 - weighted a s P.val)) :=
  (prime_summable_norm a ha s hs).of_norm.clog_one_sub.neg

theorem exp_log_euler_eq_series (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    exp (∑' P : PrimeIdeal, -log (1 - weighted a s P.val)) = series a s := by
  have hp : HasProd (fun P : PrimeIdeal => (1 - weighted a s P.val)⁻¹)
      (exp (∑' P : PrimeIdeal, -log (1 - weighted a s P.val))) :=
    (summable_neg_log_euler a ha s hs).hasSum.cexp.congr
      (fun S => Finset.prod_congr rfl (fun P _ => by
        simp only [Function.comp_apply]
        rw [exp_neg, exp_log (local_factor_ne_zero a ha s (by linarith) P)]))
  exact hp.unique (euler_hasProd a ha s hs)

def PrimeTriple (a₀ a₁ a₂ : Ideal O →*₀ ℂ) : Prop :=
  ∀ P : PrimeIdeal,
    (a₀ P.val = 0 ∧ a₁ P.val = 0 ∧ a₂ P.val = 0) ∨
    (a₀ P.val = 1 ∧ ‖a₁ P.val‖ = 1 ∧ a₂ P.val = a₁ P.val ^ 2)

theorem re_log_weighted_comb_nonneg (a₀ a₁ a₂ : Ideal O →*₀ ℂ)
    (h : PrimeTriple a₀ a₁ a₂) {x : ℝ} (hx : 1 < x) (y : ℝ) (P : PrimeIdeal) :
    0 ≤ 3 * (-log (1 - weighted a₀ (x : ℂ) P.val)).re +
      4 * (-log (1 - weighted a₁ (x + I * y) P.val)).re +
      (-log (1 - weighted a₂ (x + 2 * I * y) P.val)).re := by
  change 0 ≤ 3 * (-log (1 - a₀ P.val * normWeight (x : ℂ) P.val)).re +
      4 * (-log (1 - a₁ P.val * normWeight (x + I * y) P.val)).re +
      (-log (1 - a₂ P.val * normWeight (x + 2 * I * y) P.val)).re
  rcases h P with ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩
  · simp only [h₀, h₁, h₂, zero_mul, sub_zero, log_one, neg_zero, zero_re,
      mul_zero, add_zero, le_refl]
  · simp only [h₀, h₂, one_mul]
    change 0 ≤ 3 * (-log (1 - CubicEisenstein.fullIdealWeight (x : ℂ) P.val)).re +
      4 * (-log (1 - a₁ P.val * CubicEisenstein.fullIdealWeight (x + I * y) P.val)).re +
      (-log (1 - a₁ P.val ^ 2 * CubicEisenstein.fullIdealWeight (x + 2 * I * y) P.val)).re
    simp only [CubicEisenstein.fullIdealWeight, P.property.ne_zero, ite_false]
    exact re_log_cpow_comb_nonneg (SmoothMobiusCorrection.prime_norm_two_le P) hx y h₁

theorem norm_series_product_ge_one (a₀ a₁ a₂ : Ideal O →*₀ ℂ)
    (ha₀ : ∀ I, ‖a₀ I‖ ≤ 1) (ha₁ : ∀ I, ‖a₁ I‖ ≤ 1) (ha₂ : ∀ I, ‖a₂ I‖ ≤ 1)
    (h : PrimeTriple a₀ a₁ a₂) {x : ℝ} (hx : 1 < x) (y : ℝ) :
    1 ≤ ‖series a₀ (x : ℂ) ^ 3 * series a₁ (x + I * y) ^ 4 *
      series a₂ (x + 2 * I * y)‖ := by
  have hs₀ : 1 < (x : ℂ).re := hx
  have hs₁ : 1 < (x + I * y : ℂ).re := by simpa using hx
  have hs₂ : 1 < (x + 2 * I * y : ℂ).re := by simpa using hx
  have H₀ := summable_neg_log_euler a₀ ha₀ _ hs₀
  have H₁ := summable_neg_log_euler a₁ ha₁ _ hs₁
  have H₂ := summable_neg_log_euler a₂ ha₂ _ hs₂
  have hsum₀ := (hasSum_re H₀.hasSum).summable.mul_left 3
  have hsum₁ := (hasSum_re H₁.hasSum).summable.mul_left 4
  have hsum₂ := (hasSum_re H₂.hasSum).summable
  rw [← exp_log_euler_eq_series a₀ ha₀ _ hs₀,
    ← exp_log_euler_eq_series a₁ ha₁ _ hs₁, ← exp_log_euler_eq_series a₂ ha₂ _ hs₂]
  simp only [← exp_nat_mul, Nat.cast_ofNat, ← exp_add, norm_exp, add_re, mul_re,
    re_ofNat, im_ofNat, zero_mul, sub_zero, Real.one_le_exp_iff]
  rw [re_tsum H₀, re_tsum H₁, re_tsum H₂, ← tsum_mul_left, ← tsum_mul_left,
    ← hsum₀.tsum_add hsum₁, ← (hsum₀.add hsum₁).tsum_add hsum₂]
  exact tsum_nonneg fun P => re_log_weighted_comb_nonneg a₀ a₁ a₂ h hx y P

theorem square_unitInvariant (M : Ideal O) (χ : MulChar (O ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) : UnitInvariant M (χ ^ 2) := by
  intro u
  rw [χ.pow_apply' two_ne_zero, hχ u, one_pow]

theorem ofResidue_primeTriple (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) :
    PrimeTriple (ofResidue M 1 (one_unitInvariant M))
      (ofResidue M χ hχ) (ofResidue M (χ ^ 2) (square_unitInvariant M χ hχ)) := by
  intro P
  let q := Ideal.Quotient.mk M (Submodule.IsPrincipal.generator P.val)
  have hv (ψ : MulChar (O ⧸ M) ℂ) (hψ : UnitInvariant M ψ) :
      ofResidue M ψ hψ P.val = ψ q := by
    change value M ψ P.val = _
    have hP : P.val ≠ ⊥ := P.property.ne_zero
    simp only [value, hP, ite_false, q]
  rw [hv, hv, hv]
  by_cases hq : IsUnit q
  · right
    refine ⟨MulChar.one_apply hq, ?_, χ.pow_apply' two_ne_zero q⟩
    let : Fintype (O ⧸ M)ˣ := Fintype.ofFinite _
    obtain ⟨u, hu⟩ := hq
    rw [← hu]
    have hn := Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
    simpa only [MulChar.coe_equivToUnitHom] using hn
  · left
    exact ⟨MulChar.map_nonunit _ hq, MulChar.map_nonunit _ hq, MulChar.map_nonunit _ hq⟩

theorem norm_residue_series_product_ge_one (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) {x : ℝ} (hx : 1 < x) (y : ℝ) :
    1 ≤ ‖series (ofResidue M 1 (one_unitInvariant M)) (x : ℂ) ^ 3 *
      series (ofResidue M χ hχ) (x + I * y) ^ 4 *
      series (ofResidue M (χ ^ 2) (square_unitInvariant M χ hχ)) (x + 2 * I * y)‖ :=
  norm_series_product_ge_one _ _ _
    (norm_ofResidue_le_one M 1 (one_unitInvariant M))
    (norm_ofResidue_le_one M χ hχ)
    (norm_ofResidue_le_one M (χ ^ 2) (square_unitInvariant M χ hχ))
    (ofResidue_primeTriple M χ hχ) hx y

theorem horizontal_isBigO_of_zero (F : ℂ → ℂ) (t : ℝ)
    (hF : DifferentiableAt ℂ F (1 + I * t)) (hz : F (1 + I * t) = 0) :
    (fun x : ℝ => F (1 + x + I * t)) =O[𝓝[>] 0] fun x : ℝ => (x : ℂ) := by
  simp_rw [add_comm (1 : ℂ), add_assoc]
  have h := hF.hasDerivAt
  rw [← zero_add (1 + _)] at h
  simpa only [zero_add, hz, sub_zero]
    using (Complex.isBigO_comp_ofReal_nhds
      (h.comp_add_const 0 _).differentiableAt.isBigO_sub) |>.mono nhdsWithin_le_nhds

theorem horizontal_isBigO_one (F : ℂ → ℂ) (t : ℝ)
    (hF : ContinuousAt F (1 + I * t)) :
    (fun x : ℝ => F (1 + x + I * t)) =O[𝓝[>] 0] fun _ => (1 : ℂ) := by
  refine IsBigO.mono ?_ nhdsWithin_le_nhds
  simp_rw [add_comm (1 : ℂ), add_assoc]
  rw [← zero_add (1 + _)] at hF
  exact hF.comp (f := fun x : ℝ => x + (1 + I * t)) (x := 0) (by fun_prop)
    |>.tendsto.isBigO_one ℂ

theorem boundary_ne_zero_of_series_eq (a₀ a₁ a₂ : Ideal O →*₀ ℂ)
    (ha₀ : ∀ I, ‖a₀ I‖ ≤ 1) (ha₁ : ∀ I, ‖a₁ I‖ ≤ 1) (ha₂ : ∀ I, ‖a₂ I‖ ≤ 1)
    (h : PrimeTriple a₀ a₁ a₂) (F₀ F₁ F₂ : ℂ → ℂ)
    (hEq₀ : ∀ s : ℂ, 1 < s.re → F₀ s = series a₀ s)
    (hEq₁ : ∀ s : ℂ, 1 < s.re → F₁ s = series a₁ s)
    (hEq₂ : ∀ s : ℂ, 1 < s.re → F₂ s = series a₂ s)
    (t : ℝ)
    (hPole : (fun x : ℝ => F₀ (1 + x)) =O[𝓝[>] 0] fun x => (1 : ℂ) / x)
    (hReg₁ : DifferentiableAt ℂ F₁ (1 + I * t))
    (hReg₂ : ContinuousAt F₂ (1 + 2 * I * t)) : F₁ (1 + I * t) ≠ 0 := by
  intro hz
  have hLower (x : ℝ) (hx : 0 < x) :
      1 ≤ ‖F₀ (1 + x) ^ 3 * F₁ (1 + x + I * t) ^ 4 * F₂ (1 + x + 2 * I * t)‖ := by
    have hs₀ : 1 < (1 + x : ℂ).re := by simp; exact hx
    have hs₁ : 1 < (1 + x + I * t : ℂ).re := by simpa using hs₀
    have hs₂ : 1 < (1 + x + 2 * I * t : ℂ).re := by simpa using hs₀
    rw [hEq₀ _ hs₀, hEq₁ _ hs₁, hEq₂ _ hs₂]
    simpa only [ofReal_add, ofReal_one] using
      norm_series_product_ge_one a₀ a₁ a₂ ha₀ ha₁ ha₂ h (by linarith : 1 < 1 + x) t
  have hReg₂' : ContinuousAt F₂ (1 + I * ((2 * t : ℝ) : ℂ)) := by
    convert hReg₂ using 1
    push_cast
    ring
  have help (x : ℝ) : ((1 / x) ^ 3 * x ^ 4 * 1 : ℂ) = x := by
    rcases eq_or_ne x 0 with rfl | hx
    · rw [ofReal_zero, zero_pow (by decide), mul_zero, mul_one]
    · rw [one_div, inv_pow, pow_succ _ 3, ← mul_assoc,
        inv_mul_cancel₀ <| pow_ne_zero 3 (ofReal_ne_zero.mpr hx), one_mul, mul_one]
  have H₀ : (fun _ : ℝ => (1 : ℝ)) =O[𝓝[>] 0]
      fun x => F₀ (1 + x) ^ 3 * F₁ (1 + x + I * t) ^ 4 * F₂ (1 + x + 2 * I * t) :=
    IsBigO.of_bound' <| eventually_nhdsWithin_of_forall
      fun x hx => (norm_one (α := ℝ)).symm ▸ (hLower x hx)
  have H := (hPole.pow 3).mul ((horizontal_isBigO_of_zero F₁ t hReg₁ hz).pow 4)
    |>.mul (horizontal_isBigO_one F₂ (2 * t) hReg₂')
  simp only [ofReal_mul, ofReal_ofNat, mul_left_comm I, ← mul_assoc, help] at H
  replace H := (H₀.trans H).norm_right
  simp only [norm_real] at H
  exact isLittleO_irrefl (.of_forall (fun _ => one_ne_zero)) <|
    H.of_norm_right.trans_isLittleO <| isLittleO_id_one.mono nhdsWithin_le_nhds

section Quadratic

open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open UniqueFactorizationMonoid
open scoped ComplexOrder

def zetaConvolutionCoeff (a : Ideal O →*₀ ℂ) (B : Ideal O) : ℂ :=
  if B = 0 then 0 else ∑ D ∈ idealDivisors B, a D

theorem idealDivisors_one : idealDivisors (1 : Ideal O) = {1} := by
  ext D
  rw [mem_idealDivisors (show (1 : Ideal O) ≠ ⊥ from one_ne_zero), Finset.mem_singleton]
  exact isUnit_iff_dvd_one.symm.trans isUnit_iff_eq_one

@[simp] theorem zetaConvolutionCoeff_one (a : Ideal O →*₀ ℂ) :
    zetaConvolutionCoeff a 1 = 1 := by
  rw [zetaConvolutionCoeff, ite_eq_right one_ne_zero, idealDivisors_one, Finset.sum_singleton]
  exact map_one a

theorem idealDivisors_prime_pow (P : Ideal O) (hP : Prime P) (k : ℕ) :
    idealDivisors (P ^ k) = (Finset.range (k + 1)).image (fun j => P ^ j) := by
  ext D
  rw [mem_idealDivisors (show P ^ k ≠ ⊥ from pow_ne_zero k hP.ne_zero), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨j, hj, hDj⟩ := (dvd_prime_pow hP k).mp hD
    exact ⟨j, Finset.mem_range.mpr (by omega), (associated_iff_eq.mp hDj).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact pow_dvd_pow P (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)

theorem zetaConvolutionCoeff_prime_pow (a : Ideal O →*₀ ℂ) (P : Ideal O)
    (hP : Prime P) (k : ℕ) :
    zetaConvolutionCoeff a (P ^ k) = ∑ j ∈ Finset.range (k + 1), a P ^ j := by
  rw [zetaConvolutionCoeff, ite_eq_right (pow_ne_zero k hP.ne_zero), idealDivisors_prime_pow P hP k,
    Finset.sum_image]
  · simp only [map_pow]
  · exact fun i _ j _ hij => pow_injective_of_not_isUnit hP.not_isUnit hP.ne_zero hij

theorem zetaConvolutionCoeff_mul (a : Ideal O →*₀ ℂ) (B C : Ideal O)
    (hB : B ≠ 0) (hC : C ≠ 0) (hBC : IsRelPrime B C) :
    zetaConvolutionCoeff a (B * C) = zetaConvolutionCoeff a B * zetaConvolutionCoeff a C := by
  have hcop : IsCoprime B C := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply Ideal.isUnit_iff.mp
    exact hBC (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right)
  simp only [zetaConvolutionCoeff, hB, hC, mul_ne_zero hB hC, ite_false]
  rw [QuadraticDivisorSplit.sum_divisors_coprime_product B C hB hC hcop]
  simp only [map_mul, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem zetaConvolutionCoeff_nonneg (a : Ideal O →*₀ ℂ)
    (ha : ∀ P : Ideal O, Prime P → a P = 0 ∨ a P = 1 ∨ a P = -1)
    (B : Ideal O) : 0 ≤ zetaConvolutionCoeff a B := by
  induction B using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => simp [zetaConvolutionCoeff]
  | h1 hunit =>
    rw [isUnit_iff_eq_one.mp hunit, zetaConvolutionCoeff_one]
    exact zero_le_one
  | hpr k hP =>
    rw [zetaConvolutionCoeff_prime_pow a _ hP k]
    rcases ha _ hP with hz | ho | hm
    · exact Finset.sum_nonneg (fun j _ => by rw [hz]; exact pow_nonneg (le_refl 0) j)
    · exact Finset.sum_nonneg (fun j _ => by rw [ho, one_pow]; exact zero_le_one)
    · rw [hm, neg_one_geom_sum]
      split_ifs <;> first | exact le_refl 0 | exact zero_le_one
  | @hcp B C hBC hB hC =>
    by_cases hB0 : B = 0
    · simp [hB0, zetaConvolutionCoeff]
    by_cases hC0 : C = 0
    · simp [hC0, zetaConvolutionCoeff]
    rw [zetaConvolutionCoeff_mul a B C hB0 hC0 hBC]
    exact mul_nonneg hB hC

theorem quadratic_normFiber_nonneg (M : Ideal O) (χ : MulChar (O ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) (hquad : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ ShortDraftHeckeBridge.normFiberCoeff
      (zetaConvolutionCoeff (ofResidue M χ hχ)) n := by
  apply Finset.sum_nonneg
  intro B _
  apply zetaConvolutionCoeff_nonneg
  intro P hP
  change value M χ P = 0 ∨ value M χ P = 1 ∨ value M χ P = -1
  have hP0 : P ≠ ⊥ := hP.ne_zero
  simp only [value, hP0, ite_false]
  exact MulChar.isQuadratic_iff_sq_eq_one.mpr hquad _

theorem mulFiber_character_sum (a : Ideal O →*₀ ℂ) (B : Ideal O) (hB : B ≠ 0) :
    (∑' p : CompletedGauss.MulFiber B, a p.val.1) = zetaConvolutionCoeff a B := by
  let e := CompletedGauss.mulFiberDivisorEquiv B hB
  rw [zetaConvolutionCoeff, ite_eq_right hB]
  calc
    _ = ∑' D : {D : Ideal O // D ∈ idealDivisors B}, a D.val :=
      e.tsum_eq (fun D => a D.val)
    _ = _ := by
      rw [tsum_fintype]
      exact (Finset.sum_subtype (idealDivisors B) (fun _ => Iff.rfl) a).symm

theorem zetaConvolution_hasSum (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun B : Ideal O => zetaConvolutionCoeff a B * normWeight s B)
      (series a s * CubicEisenstein.fullIdealZeta s) := by
  let F : Ideal O × Ideal O → ℂ := fun p => a p.1 * normWeight s (p.1 * p.2)
  have hprod := (weighted_summable_norm a ha s hs).mul_norm
    (CubicEisenstein.fullIdealWeight_summable_norm s hs)
  have heq (p : Ideal O × Ideal O) :
      weighted a s p.1 * CubicEisenstein.fullIdealWeight s p.2 = F p := by
    change (a p.1 * normWeight s p.1) * normWeight s p.2 = _
    simp only [F, map_mul, mul_assoc]
  have hF : Summable F := hprod.of_norm.congr heq
  have hfiber (B : Ideal O) : (∑' p : CompletedGauss.MulFiber B, F p.val) =
      zetaConvolutionCoeff a B * normWeight s B := by
    by_cases hB : B = 0
    · subst B
      have hz (p : CompletedGauss.MulFiber 0) : F p.val = 0 := by
        simp only [F, p.property, map_zero, mul_zero]
      simp only [hz, tsum_zero, map_zero, mul_zero]
    · calc
        _ = (∑' p : CompletedGauss.MulFiber B, a p.val.1) * normWeight s B := by
          rw [← tsum_mul_right]
          exact tsum_congr (fun p => by simp only [F, p.property])
        _ = _ := by rw [mulFiber_character_sum a B hB]
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1 * p.2)
  change HasSum (fun B : Ideal O => ∑' p : CompletedGauss.MulFiber B, F p.val) _ at hsum
  simp_rw [hfiber] at hsum
  convert hsum using 1
  calc
    _ = ∑' p : Ideal O × Ideal O,
        weighted a s p.1 * CubicEisenstein.fullIdealWeight s p.2 :=
      tsum_mul_tsum_of_summable_norm (weighted_summable_norm a ha s hs)
        (CubicEisenstein.fullIdealWeight_summable_norm s hs)
    _ = _ := tsum_congr heq

theorem zetaConvolution_normFiber_one (a : Ideal O →*₀ ℂ) :
    ShortDraftHeckeBridge.normFiberCoeff (zetaConvolutionCoeff a) 1 = 1 := by
  have hsingle : (Ideal.finite_setOfPred_absNorm_eq (S := O) 1).toFinset = {1} := by
    ext I
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_singleton]
    exact Ideal.absNorm_eq_one_iff.trans (by rw [Ideal.one_eq_top])
  unfold ShortDraftHeckeBridge.normFiberCoeff
  rw [hsingle, Finset.sum_singleton, zetaConvolutionCoeff_one]

theorem zetaConvolution_LSeries_hasSum (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (LSeries.term (ShortDraftHeckeBridge.normFiberCoeff (zetaConvolutionCoeff a)) s)
      (series a s * CubicEisenstein.fullIdealZeta s) := by
  have h := (zetaConvolution_hasSum a ha s hs).tsum_fiberwise Ideal.absNorm
  change HasSum (fun n : ℕ => ∑' I : {I : Ideal O // Ideal.absNorm I = n},
    zetaConvolutionCoeff a I.val * CubicEisenstein.fullIdealWeight s I.val) _ at h
  simpa only [SmoothMobiusCorrection.idealDirichlet_fiber] using h

theorem zetaConvolution_LSeries_eq (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    LSeries (ShortDraftHeckeBridge.normFiberCoeff (zetaConvolutionCoeff a)) s =
      series a s * CubicEisenstein.fullIdealZeta s :=
  (zetaConvolution_LSeries_hasSum a ha s hs).tsum_eq

theorem quadratic_product_positive (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (hquad : χ ^ 2 = 1)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hEq : ∀ s : ℂ, 1 < s.re →
      F s = series (ofResidue M χ hχ) s * CubicEisenstein.fullIdealZeta s) (y : ℝ) :
    0 < F y := by
  refine LSeries.positive_of_differentiable_of_eqOn
    (quadratic_normFiber_nonneg M χ hχ hquad)
    (zetaConvolution_normFiber_one (ofResidue M χ hχ) ▸ zero_lt_one) hF
    (x := 1) ?_ ?_ y
  · exact LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun s hs => (zetaConvolution_LSeries_hasSum (ofResidue M χ hχ)
        (norm_ofResidue_le_one M χ hχ) s hs).summable)
  · intro s hs
    rw [hEq s hs, zetaConvolution_LSeries_eq (ofResidue M χ hχ)
      (norm_ofResidue_le_one M χ hχ) s hs]

theorem fullIdealZeta_eq_dirichlet_product (s : ℂ) (hs : 1 < s.re) :
    CubicEisenstein.fullIdealZeta s = riemannZeta s *
      (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1)).LFunction s := by
  let a := normWeight 0
  have ha (I : Ideal O) : ‖a I‖ ≤ 1 := by
    by_cases hI : I = ⊥ <;> simp [a, normWeight, CubicEisenstein.fullIdealWeight, hI]
  have hchar (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 := by
    rw [Subsingleton.elim (n : ZMod 1) 1, map_one]
  have hseries : series a s = CubicEisenstein.fullIdealZeta s := by
    apply tsum_congr
    intro I
    by_cases hI : I = ⊥ <;>
      simp [weighted, a, normWeight, CubicEisenstein.fullIdealWeight, hI]
  have hinverse : inverseSeries a s =
      LSeries (ShortDraftHeckeBridge.pairInverseCoeff (1 : DirichletCharacter ℂ 1)
        (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1))) s := by
    rw [← ShortDraftHeckeBridge.normFiber_LSeries_eq_pair_inverse
      (1 : DirichletCharacter ℂ 1) (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1))
      (ShortDraftHeckeBridge.baseChangeWeight (1 : DirichletCharacter ℂ 1))
      (ShortDraftHeckeBridge.normFiberCoeff_baseChange_eq_pairInverseCoeff (1 : DirichletCharacter ℂ 1)) s]
    rw [← SmoothMobiusCorrection.idealDirichlet_eq_LSeries
      (ShortDraftHeckeBridge.baseChangeWeight (1 : DirichletCharacter ℂ 1))
      (ConcretePrimeRowBridge.baseChangeWeight_norm_le_one (1 : DirichletCharacter ℂ 1)) s hs]
    apply tsum_congr
    intro I
    by_cases hI : I = ⊥ <;>
      simp [weighted, a, normWeight, CubicEisenstein.fullIdealWeight,
        ShortDraftHeckeBridge.baseChangeWeight, hI, hchar]
  have hi := inverseSeries_mul_series a ha s hs
  have hp := ShortDraftHeckeBridge.pair_inverse_euler_identity
    (1 : DirichletCharacter ℂ 1) (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1)) s hs
  rw [← hinverse, DirichletCharacter.LFunction_modOne_eq] at hp
  rw [← hseries]
  calc
    series a s = 1 * series a s := (one_mul _).symm
    _ = ((riemannZeta s *
        (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1)).LFunction s) *
          inverseSeries a s) * series a s := by rw [hp]
    _ = _ := by rw [mul_assoc, hi, mul_one]

def regularizedIdealZeta (s : ℂ) : ℂ :=
  DirichletCharacter.LFunctionTrivChar₁ 1 s *
    (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1)).LFunction s

theorem regularizedIdealZeta_differentiable : Differentiable ℂ regularizedIdealZeta :=
  (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).mul
    (DirichletCharacter.differentiable_LFunction
      (ShortDraftHeckeBridge.baseChangeChar_ne_one_of_one
        (1 : DirichletCharacter ℂ 1) rfl))

theorem regularizedIdealZeta_eq (s : ℂ) (hs : 1 < s.re) :
    regularizedIdealZeta s = (s - 1) * CubicEisenstein.fullIdealZeta s := by
  have hs1 : s ≠ 1 := by intro he; simp only [he, one_re, lt_self_iff_false] at hs
  rw [regularizedIdealZeta, DirichletCharacter.LFunctionTrivChar₁,
    Function.update_of_ne hs1, DirichletCharacter.LFunctionTrivChar,
    DirichletCharacter.LFunction_modOne_eq, fullIdealZeta_eq_dirichlet_product s hs,
    mul_assoc]

theorem regularizedIdealZeta_neg_two : regularizedIdealZeta (-2 : ℝ) = 0 := by
  have hz := riemannZeta_neg_two_mul_nat_add_one 0
  rw [Nat.cast_zero, zero_add, mul_one] at hz
  rw [regularizedIdealZeta, DirichletCharacter.LFunctionTrivChar₁,
    Function.update_of_ne (by norm_num : (-2 : ℝ) ≠ (1 : ℂ)),
    DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq]
  simp only [ofReal_neg, ofReal_ofNat, hz, mul_zero, zero_mul]

theorem differentiable_dslope_of_entire (F : ℂ → ℂ) (hF : Differentiable ℂ F) (c : ℂ) :
    Differentiable ℂ (dslope F c) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (Filter.univ_mem : Set.univ ∈ 𝓝 c)).mpr
    hF.differentiableOn

theorem quadratic_one_ne_zero_of_regularized_zeta (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (hquad : χ ^ 2 = 1)
    (L R : ℂ → ℂ) (hL : Differentiable ℂ L) (hR : Differentiable ℂ R)
    (hLeq : ∀ s : ℂ, 1 < s.re → L s = series (ofResidue M χ hχ) s)
    (hReq : ∀ s : ℂ, 1 < s.re → R s = (s - 1) * CubicEisenstein.fullIdealZeta s)
    (y : ℝ) (hRy : R y = 0) : L 1 ≠ 0 := by
  intro hz
  let F : ℂ → ℂ := fun s => R s * dslope L 1 s
  have hF : Differentiable ℂ F := hR.mul (differentiable_dslope_of_entire L hL 1)
  have hEq (s : ℂ) (hs : 1 < s.re) :
      F s = series (ofResidue M χ hχ) s * CubicEisenstein.fullIdealZeta s := by
    have hs1 : s ≠ 1 := by intro he; simp only [he, one_re, lt_self_iff_false] at hs
    dsimp only [F]
    rw [hReq s hs, dslope_of_ne L hs1, slope, smul_eq_mul, vsub_eq_sub, hz, sub_zero,
      hLeq s hs]
    field_simp
  have hpos := quadratic_product_positive M χ hχ hquad F hF hEq y
  have hzero : F y = 0 := by simp only [F, hRy, zero_mul]
  exact hzero.not_gt hpos

theorem quadratic_one_ne_zero_of_entire (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (hquad : χ ^ 2 = 1)
    (L : ℂ → ℂ) (hL : Differentiable ℂ L)
    (hLeq : ∀ s : ℂ, 1 < s.re → L s = series (ofResidue M χ hχ) s) : L 1 ≠ 0 :=
  quadratic_one_ne_zero_of_regularized_zeta M χ hχ hquad L regularizedIdealZeta hL
    regularizedIdealZeta_differentiable hLeq regularizedIdealZeta_eq (-2)
    regularizedIdealZeta_neg_two

theorem normWeight_real_nonneg (x : ℝ) (B : Ideal O) : 0 ≤ normWeight (x : ℂ) B := by
  change 0 ≤ CubicEisenstein.fullIdealWeight (x : ℂ) B
  unfold CubicEisenstein.fullIdealWeight
  split_ifs
  · exact le_rfl
  · rw [← ofReal_natCast, ← ofReal_neg, ← ofReal_cpow (Nat.cast_nonneg _)]
    exact_mod_cast Real.rpow_nonneg (Nat.cast_nonneg (Ideal.absNorm B)) (-x)

theorem norm_series_le_norm_fullIdealZeta (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (x : ℝ) (hx : 1 < x) : ‖series a (x : ℂ)‖ ≤ ‖CubicEisenstein.fullIdealZeta (x : ℂ)‖ := by
  have hs : 1 < (x : ℂ).re := hx
  have hweight (I : Ideal O) :
      CubicEisenstein.fullIdealWeight (x : ℂ) I = (‖CubicEisenstein.fullIdealWeight (x : ℂ) I‖ : ℂ) :=
    eq_coe_norm_of_nonneg (normWeight_real_nonneg x I)
  have hnorm : ‖CubicEisenstein.fullIdealZeta (x : ℂ)‖ =
      ∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight (x : ℂ) I‖ := by
    unfold CubicEisenstein.fullIdealZeta
    rw [tsum_congr hweight, ← ofReal_tsum,
      Complex.norm_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]
  rw [hnorm]
  refine (norm_tsum_le_tsum_norm (weighted_summable_norm a ha _ hs)).trans ?_
  apply Summable.tsum_le_tsum _ (weighted_summable_norm a ha _ hs)
    (CubicEisenstein.fullIdealWeight_summable_norm _ hs)
  intro I
  change ‖a I * CubicEisenstein.fullIdealWeight (x : ℂ) I‖ ≤ _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha I)

theorem fullIdealZeta_isBigO_near_one_horizontal :
    (fun x : ℝ => CubicEisenstein.fullIdealZeta (1 + x)) =O[𝓝[>] 0]
      fun x => (1 : ℂ) / x := by
  have hR : (fun x : ℝ => regularizedIdealZeta (1 + x)) =O[𝓝[>] 0]
      fun _ => (1 : ℂ) := by
    simpa only [ofReal_zero, mul_zero, add_zero] using horizontal_isBigO_one
      regularizedIdealZeta 0 (by simpa using (regularizedIdealZeta_differentiable 1).continuousAt)
  have hB : (fun x : ℝ => (x : ℂ) * CubicEisenstein.fullIdealZeta (1 + x)) =O[𝓝[>] 0]
      fun _ => (1 : ℂ) := hR.congr'
    (eventually_nhdsWithin_of_forall (fun x hx => by
      dsimp only
      rw [regularizedIdealZeta_eq _ (by simpa using hx), add_sub_cancel_left]))
    (Filter.EventuallyEq.refl _ _)
  exact (isBigO_mul_iff_isBigO_div (eventually_nhdsWithin_of_forall
    (fun x hx => ofReal_ne_zero.mpr (ne_of_gt hx)))).mp hB

theorem series_isBigO_near_one_horizontal (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) :
    (fun x : ℝ => series a (1 + x)) =O[𝓝[>] 0] fun x => (1 : ℂ) / x := by
  have h : (fun x : ℝ => series a (1 + x)) =O[𝓝[>] 0]
      fun x => CubicEisenstein.fullIdealZeta (1 + x) := by
    apply IsBigO.of_bound'
    apply eventually_nhdsWithin_of_forall
    intro x hx
    change 0 < x at hx
    simpa only [ofReal_add, ofReal_one] using
      norm_series_le_norm_fullIdealZeta a ha (1 + x) (by linarith)
  exact h.trans fullIdealZeta_isBigO_near_one_horizontal

theorem residue_boundary_ne_zero_of_series_eq (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (L L₂ : ℂ → ℂ)
    (hEq : ∀ s : ℂ, 1 < s.re → L s = series (ofResidue M χ hχ) s)
    (hEq₂ : ∀ s : ℂ, 1 < s.re → L₂ s =
      series (ofResidue M (χ ^ 2) (square_unitInvariant M χ hχ)) s)
    (t : ℝ) (hL : DifferentiableAt ℂ L (1 + I * t))
    (hL₂ : ContinuousAt L₂ (1 + 2 * I * t)) : L (1 + I * t) ≠ 0 :=
  boundary_ne_zero_of_series_eq
    (ofResidue M 1 (one_unitInvariant M)) (ofResidue M χ hχ)
    (ofResidue M (χ ^ 2) (square_unitInvariant M χ hχ))
    (norm_ofResidue_le_one M 1 (one_unitInvariant M))
    (norm_ofResidue_le_one M χ hχ)
    (norm_ofResidue_le_one M (χ ^ 2) (square_unitInvariant M χ hχ))
    (ofResidue_primeTriple M χ hχ)
    (series (ofResidue M 1 (one_unitInvariant M))) L L₂ (fun _ _ => rfl)
    hEq hEq₂ t
    (series_isBigO_near_one_horizontal _ (norm_ofResidue_le_one M 1 (one_unitInvariant M)))
    hL hL₂

end Quadratic

end

end SevenEighths.HeckeBoundary

end OAI

end Source465

/- Original source: OAI/NumberTheory/DirichletL/Hecke/BoundaryIntegration.lean; sha256: 404bb346650e5a84f6e839eaee1c4598b45296af0dcaeacd2bc6a5a0470a5045 -/
section Source466
namespace OAI

noncomputable section
namespace SevenEighths.HeckeFamily

theorem LFunction_one_ne_zero_quadratic (χ : Character)
    (hχ : χ.residue ≠ 1) (hquad : χ.residue ^ 2 = 1) : LFunction χ 1 ≠ 0 := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  exact HeckeBoundary.quadratic_one_ne_zero_of_entire χ.modulus χ.residue
    χ.unit_trivial hquad (LFunction χ) (LFunction_entire_nonprincipal χ hχ)
      (fun s hs => LFunction_eq_series χ hs)

theorem LFunction_boundary_ne_zero (χ : Character) (t : ℝ)
    (hpole : t ≠ 0 ∨ χ.residue ≠ 1)
    (hsquare : t ≠ 0 ∨ χ.residue ^ 2 ≠ 1) :
    LFunction χ (1 + Complex.I * t) ≠ 0 := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  have h1 (t : ℝ) (ht : t ≠ 0) : (1 + Complex.I * t : ℂ) ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul,
      zero_add] at hi
    exact ht hi
  have h0 (t : ℝ) : (1 + Complex.I * t : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  apply HeckeBoundary.residue_boundary_ne_zero_of_series_eq χ.modulus χ.residue
    χ.unit_trivial (LFunction χ) (LFunction (χ.power 2))
    (fun s hs => LFunction_eq_series χ hs)
    (fun s hs => LFunction_eq_series (χ.power 2) hs) t
  · apply LFunction_differentiableAt χ (h0 t)
    exact hpole.imp (h1 t) id
  · have heq : (1 + 2 * Complex.I * t : ℂ) = 1 + Complex.I * (2 * t : ℝ) := by
      push_cast
      ring
    rw [heq]
    apply DifferentiableAt.continuousAt (𝕜 := ℂ)
    apply LFunction_differentiableAt (χ.power 2) (h0 (2*t))
    rcases hsquare with ht | hsq
    · exact Or.inl (h1 (2*t) (mul_ne_zero (by norm_num) ht))
    · exact Or.inr hsq

theorem LFunction_one_ne_zero_nonprincipal (χ : Character) (hχ : χ.residue ≠ 1) :
    LFunction χ 1 ≠ 0 := by
  by_cases hquad : χ.residue ^ 2 = 1
  · exact LFunction_one_ne_zero_quadratic χ hχ hquad
  · simpa only [Complex.ofReal_zero, mul_zero, add_zero] using
      LFunction_boundary_ne_zero χ 0 (Or.inr hχ) (Or.inr hquad)

theorem LFunction_ne_zero_of_re_eq_one (χ : Character) {s : ℂ}
    (hs : s.re = 1) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ s ≠ 0 := by
  have heq : s = 1 + Complex.I * s.im := by
    apply Complex.ext <;> simp [hs]
  by_cases ht : s.im = 0
  · have hs1 : s = 1 := by rw [heq, ht]; simp
    subst s
    exact LFunction_one_ne_zero_nonprincipal χ (hpole.resolve_left (not_not.mpr rfl))
  · rw [heq]
    exact LFunction_boundary_ne_zero χ s.im (Or.inl ht) (Or.inl ht)

theorem LFunction_ne_zero_of_one_le_re (χ : Character) {s : ℂ}
    (hs : 1 ≤ s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ s ≠ 0 := by
  rcases eq_or_lt_of_le hs with h | h
  · exact LFunction_ne_zero_of_re_eq_one χ h.symm hpole
  · exact LFunction_ne_zero_of_one_lt_re χ h

end SevenEighths.HeckeFamily

end

end OAI

end Source466

/- Original source: OAI/NumberTheory/DirichletL/Hecke/MellinIdentity.lean; sha256: 8b1f94243f41d7c3ff5389878798161c84f0fef545fd5d28c277d805ccae1f14 -/
section Source467
namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace SevenEighths.HeckeMellinIdentity

def regularized (P : WeakFEPair ℂ) (s : ℂ) : ℂ :=
  s * (s - 1) * P.Λ₀ s - (s - 1) * P.f₀ + s * P.ε * P.g₀

theorem regularized_entire (P : WeakFEPair ℂ) : Differentiable ℂ (regularized P) := by
  unfold regularized
  have hd := P.differentiable_Λ₀
  fun_prop

theorem regularized_eq (P : WeakFEPair ℂ) (hk : P.k = 1) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) : regularized P s = s * (s-1) * P.Λ s := by
  unfold regularized WeakFEPair.Λ
  rw [hk]
  simp only [smul_eq_mul, Complex.ofReal_one]
  have h1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  ring

theorem scaled_eq (P Q : WeakFEPair ℂ) (hP : P.k = 1) (hQ : Q.k = 1)
    (A : ℝ) (hA : 0 < A)
    (hright : ∀ s : ℂ, 1 < s.re → P.Λ s = (A : ℂ)^(-s) * Q.Λ s)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    P.Λ s = (A : ℂ)^(-s) * Q.Λ s := by
  have hd : Differentiable ℂ (fun z : ℂ => (A : ℂ)^(-z) * regularized Q z) :=
    ((differentiable_id.neg).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hA.ne'))).mul (regularized_entire Q)
  have he : regularized P = fun z : ℂ => (A : ℂ)^(-z) * regularized Q z := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr (regularized_entire P)).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hd) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
    have hz1 : z ≠ 1 := by intro h; norm_num [h] at hz
    rw [regularized_eq P hP hz0 hz1, regularized_eq Q hQ hz0 hz1, hright z hz]
    ring
  have heq := congr_fun he s
  rw [regularized_eq P hP h0 h1, regularized_eq Q hQ h0 h1] at heq
  apply mul_left_cancel₀ (mul_ne_zero h0 (sub_ne_zero.mpr h1))
  calc
    s * (s - 1) * P.Λ s = (A : ℂ)^(-s) * (s * (s-1) * Q.Λ s) := heq
    _ = s * (s-1) * ((A : ℂ)^(-s) * Q.Λ s) := by ring

theorem eq_of_f (P Q : WeakFEPair ℂ) (hP : P.k = 1) (hQ : Q.k = 1)
    (hf : ∀ t : ℝ, 0 < t → P.f t = Q.f t) (hf₀ : P.f₀ = Q.f₀)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : P.Λ s = Q.Λ s := by
  have h := scaled_eq P Q hP hQ 1 zero_lt_one (fun z hz => by
    simp only [Complex.ofReal_one, Complex.one_cpow, one_mul]
    rw [← (P.hasMellin (by rwa [hP])).2, ← (Q.hasMellin (by rwa [hQ])).2]
    unfold mellin
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [hf t ht, hf₀]) h0 h1
  simpa only [Complex.ofReal_one, Complex.one_cpow, one_mul] using h

end SevenEighths.HeckeMellinIdentity

end

end OAI

end Source467

/- Original source: OAI/NumberTheory/DirichletL/Hecke/Origin.lean; sha256: 6ff6b0c08619fc86f0ebb63c3ba9d6bdb2e14cff8a4328a85fb9e00e73af9f2f -/
section Source468
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeOrigin
open HeckeFamily HeckeTheta

def poleRemoved (χ : Character) (s : ℂ) : ℂ :=
  (Real.pi : ℂ)^s * (Complex.Gamma (s+1))⁻¹ *
    HeckeMellinIdentity.regularized (pair (coefficients χ)) s / 6

theorem poleRemoved_entire (χ : Character) : Differentiable ℂ (poleRemoved χ) := by
  have hGamma : Differentiable ℂ (fun s : ℂ => (Complex.Gamma (s+1))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const 1)
  exact (((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul hGamma).mul
      (HeckeMellinIdentity.regularized_entire _)).div_const 6

theorem poleRemoved_eq (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    poleRemoved χ s = (s-1) * LFunction χ s := by
  unfold poleRemoved LFunction continuedLattice latticeL completed
  rw [HeckeMellinIdentity.regularized_eq _ (pair_k _) h0 h1,
    Complex.Gamma_add_one s h0, mul_inv_rev]
  field_simp

theorem poleRemoved_zero (χ : Character) :
    poleRemoved χ 0 = coefficients χ (0,0) / 6 := by
  simp [poleRemoved, HeckeMellinIdentity.regularized, pair_f₀]

theorem poleRemoved_one (χ : Character) :
    poleRemoved χ 1 = HeckeReciprocal.regularizedL χ 1 := by
  rw [HeckeReciprocal.regularizedL_at_one]
  simp [poleRemoved, HeckeMellinIdentity.regularized,
    Complex.Gamma_add_one 1 one_ne_zero,
    show (pair (coefficients χ)).ε = 1 from rfl]

theorem poleRemoved_one_ne_zero (χ : Character) (hχ : χ.residue = 1) :
    poleRemoved χ 1 ≠ 0 := by
  rw [poleRemoved_one]
  exact HeckeReciprocal.regularizedL_ne_zero_at_one χ hχ

def continued (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue = 1 then poleRemoved χ s / (s-1) else LFunction χ s

theorem continued_eq (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    continued χ s = LFunction χ s := by
  unfold continued
  split_ifs
  · rw [poleRemoved_eq χ h0 h1, mul_div_cancel_left₀ _ (sub_ne_zero.mpr h1)]
  · rfl

theorem continued_differentiableAt (χ : Character) {s : ℂ}
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : DifferentiableAt ℂ (continued χ) s := by
  by_cases hχ : χ.residue = 1
  · have heq : continued χ = fun z => poleRemoved χ z / (z-1) := by
      funext z
      simp [continued, hχ]
    rw [heq]
    exact (poleRemoved_entire χ s).div (differentiableAt_id.sub_const 1)
      (sub_ne_zero.mpr (hpole.resolve_right (not_not.mpr hχ)))
  · have heq : continued χ = LFunction χ := by
      funext z
      simp [continued, hχ]
    rw [heq]
    exact ((HeckeCharacterAnalytic.continuedLattice_entire_nonprincipal χ hχ).div_const 6) s

theorem continued_zero (χ : Character) : continued χ 0 = -coefficients χ (0,0) / 6 := by
  by_cases hχ : χ.residue = 1
  · simp [continued, hχ, poleRemoved_zero]
    ring
  · rw [HeckeCharacterAnalytic.coefficients_zero_of_nonprincipal χ hχ]
    simp [continued, hχ, LFunction, continuedLattice, latticeL, Complex.Gamma_zero]

end SevenEighths.HeckeOrigin

end

end OAI

end Source468

/- Original source: OAI/NumberTheory/DirichletL/IdealMangoldt.lean; sha256: c705c91104e26af00cc38fba2cd83c91f8587c68e4ae886979e14a441007446f -/
section Source469
namespace OAI

namespace SevenEighths.IdealMangoldt

open ActualEisensteinCubic UniqueFactorizationMonoid ArithmeticFunction
open scoped BigOperators Classical

noncomputable section

def primeBase (I : Ideal O) : Ideal O := if h : IsPrimePow I then h.choose else 1

theorem primeBase_spec {I : Ideal O} (hI : IsPrimePow I) :
    Prime (primeBase I) ∧ ∃ k : ℕ, 0 < k ∧ primeBase I ^ k = I := by
  obtain ⟨k, hp, hk, heq⟩ := hI.choose_spec
  simp only [primeBase, hI, dite_true]
  exact ⟨hp, k, hk, heq⟩

theorem primeBase_pow {P : Ideal O} (hP : Prime P) {k : ℕ} (hk : 0 < k) :
    primeBase (P ^ k) = P := by
  have hpow : IsPrimePow (P ^ k) := ⟨P, k, hP, hk, rfl⟩
  obtain ⟨hQ, l, hl, heq⟩ := primeBase_spec hpow
  apply associated_iff_eq.mp
  apply hQ.associated_of_dvd hP
  exact hQ.dvd_of_dvd_pow (heq ▸ dvd_pow_self (primeBase (P ^ k)) hl.ne')

def value (I : Ideal O) : ℝ :=
  if IsPrimePow I then Real.log (Ideal.absNorm (primeBase I)) else 0

@[simp] theorem value_zero : value (0 : Ideal O) = 0 := by
  simp only [value, not_isPrimePow_zero, ite_false]

@[simp] theorem value_one : value (1 : Ideal O) = 0 := by
  simp only [value, not_isPrimePow_one, ite_false]

theorem value_pow {P : Ideal O} (hP : Prime P) {k : ℕ} (hk : 0 < k) :
    value (P ^ k) = Real.log (Ideal.absNorm P) := by
  rw [value, ite_eq_left (show IsPrimePow (P ^ k) from ⟨P, k, hP, hk, rfl⟩),
    primeBase_pow hP hk]

theorem value_nonneg (I : Ideal O) : 0 ≤ value I := by
  by_cases hI : IsPrimePow I
  · rw [value, ite_eq_left hI]
    apply Real.log_nonneg
    exact_mod_cast (SmoothMobiusCorrection.prime_norm_two_le ⟨_, (primeBase_spec hI).1⟩).trans' (by decide : 1 ≤ 2)
  · simp only [value, hI, ite_false, le_refl]

theorem isPrimePow_absNorm {I : Ideal O} (hI : IsPrimePow I) :
    IsPrimePow (Ideal.absNorm I) := by
  obtain ⟨P, k, hP, hk, rfl⟩ := hI
  let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  obtain ⟨p, n, hn, _, hp, hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
  rw [map_pow, hnorm, ← pow_mul]
  exact (isPrimePow_nat_iff _).mpr ⟨p, n * k, hp, mul_pos hn hk, rfl⟩

theorem value_eq_zero_of_norm_not_primePow {I : Ideal O}
    (hI : ¬IsPrimePow (Ideal.absNorm I)) : value I = 0 := by
  exact ite_eq_right (fun h => hI (isPrimePow_absNorm h))

theorem prime_mem_primesOver_of_dvd_norm {P : Ideal O} (hP : Prime P)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ Ideal.absNorm P) :
    P ∈ (Ideal.span {(p : ℤ)}).primesOver O := by
  obtain ⟨Q, hQ, hQu, hQP⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp P hd
  have heq : P = Q := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero |>.eq_of_le
    hQ.ne_top (Ideal.dvd_iff_le.mp hQP)
  subst Q
  exact ⟨Ideal.isPrime_of_prime hP, ⟨hQu.symm⟩⟩

theorem primeBase_mem_primesOver {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    {I : Ideal O} (hI : IsPrimePow I) (hn : Ideal.absNorm I = p ^ k) :
    primeBase I ∈ (Ideal.span {(p : ℤ)}).primesOver O := by
  obtain ⟨hP, l, hl, heq⟩ := primeBase_spec hI
  apply prime_mem_primesOver_of_dvd_norm hP hp
  apply hp.dvd_of_dvd_pow
  have hnorm := congrArg Ideal.absNorm heq
  rw [map_pow, hn] at hnorm
  rw [hnorm]
  exact dvd_pow_self _ hk.ne'

theorem primeBase_injective_on_norm {I J : Ideal O} (hI : IsPrimePow I)
    (hJ : IsPrimePow J) (hn : Ideal.absNorm I = Ideal.absNorm J)
    (hbase : primeBase I = primeBase J) : I = J := by
  obtain ⟨hP, k, hk, hPk⟩ := primeBase_spec hI
  obtain ⟨_, l, hl, hPl⟩ := primeBase_spec hJ
  rw [← hbase] at hPl
  have hkl : k = l := by
    apply Nat.pow_right_injective (SmoothMobiusCorrection.prime_norm_two_le ⟨_, hP⟩)
    have hnI : Ideal.absNorm (primeBase I) ^ k = Ideal.absNorm I := by
      simpa only [map_pow] using congrArg Ideal.absNorm hPk
    have hnJ : Ideal.absNorm (primeBase I) ^ l = Ideal.absNorm J := by
      simpa only [map_pow] using congrArg Ideal.absNorm hPl
    exact hnI.trans (hn.trans hnJ.symm)
  exact hPk.symm.trans ((congrArg (primeBase I ^ ·) hkl).trans hPl)

def normFiber (n : ℕ) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset

@[simp] theorem mem_normFiber (n : ℕ) (I : Ideal O) : I ∈ normFiber n ↔ Ideal.absNorm I = n :=
  Set.Finite.mem_toFinset _

def coeff (w : Ideal O → ℝ) (n : ℕ) : ℝ := ∑ I ∈ normFiber n, w I * value I

theorem coeff_nonneg (w : Ideal O → ℝ) (hw : ∀ I, 0 ≤ w I) (n : ℕ) :
    0 ≤ coeff w n :=
  Finset.sum_nonneg (fun I _ => mul_nonneg (hw I) (value_nonneg I))

theorem coeff_le_unweighted (w : Ideal O → ℝ) (hw : ∀ I, w I ≤ 1) (n : ℕ) :
    coeff w n ≤ coeff (fun _ => 1) n := by
  apply Finset.sum_le_sum
  intro I hI
  exact mul_le_mul_of_nonneg_right (hw I) (value_nonneg I)

theorem coeff_eq_sum_primePowers (n : ℕ) :
    coeff (fun _ => 1) n =
      ∑ I ∈ (normFiber n).filter IsPrimePow, Real.log (Ideal.absNorm (primeBase I)) := by
  simp only [coeff, one_mul, value, Finset.sum_filter]

theorem coeff_eq_zero_of_not_primePow {n : ℕ} (hn : ¬IsPrimePow n)
    (w : Ideal O → ℝ) : coeff w n = 0 := by
  apply Finset.sum_eq_zero
  intro I hI
  rw [value_eq_zero_of_norm_not_primePow (by simpa only [(mem_normFiber n I).mp hI] using hn),
    mul_zero]

def primesOver (p : ℕ) [Fact p.Prime] : Finset (Ideal O) :=
  (IsDedekindDomain.primesOver_finite (Ideal.span {(p : ℤ)}) O).toFinset

@[simp] theorem mem_primesOver (p : ℕ) [Fact p.Prime] (P : Ideal O) :
    P ∈ primesOver p ↔ P ∈ (Ideal.span {(p : ℤ)}).primesOver O :=
  Set.Finite.mem_toFinset _

theorem primesOver_card (p : ℕ) [Fact p.Prime] :
    (primesOver p).card = ((Ideal.span {(p : ℤ)}).primesOver O).ncard := by
  exact (Set.ncard_eq_toFinset_card _).symm

theorem primesOver_log_sum_le (p : ℕ) [hp : Fact p.Prime] :
    ∑ P ∈ primesOver p, Real.log (Ideal.absNorm P) ≤ 2 * Real.log p := by
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.out.one_lt.le)
  by_cases h1 : p % 3 = 1
  · have hv (P : Ideal O) (hP : P ∈ primesOver p) :
        Real.log (Ideal.absNorm P) = Real.log p := by
      have hPP := (mem_primesOver p P).mp hP
      let : P.IsPrime := hPP.1
      let : P.LiesOver (Ideal.span {(p : ℤ)}) := hPP.2
      rw [ShortDraftHeckeBridge.absNorm_split hp.out h1 P]
    rw [Finset.sum_congr rfl hv, Finset.sum_const, nsmul_eq_mul, primesOver_card,
      ShortDraftHeckeBridge.split_count_of_mod_one hp.out h1]
    norm_num
  by_cases h2 : p % 3 = 2
  · have hv (P : Ideal O) (hP : P ∈ primesOver p) :
        Real.log (Ideal.absNorm P) = 2 * Real.log p := by
      have hPP := (mem_primesOver p P).mp hP
      let : P.IsPrime := hPP.1
      let : P.LiesOver (Ideal.span {(p : ℤ)}) := hPP.2
      rw [ShortDraftHeckeBridge.absNorm_inert hp.out h2 P, Nat.cast_pow, Real.log_pow]
      norm_num
    rw [Finset.sum_congr rfl hv, Finset.sum_const, nsmul_eq_mul, primesOver_card,
      ShortDraftHeckeBridge.inert_count_of_mod_two hp.out h2]
    norm_num
  have h3 : p = 3 := by
    have h0 : p % 3 = 0 := by have := Nat.mod_lt p (by decide : 0 < 3); omega
    have h := (Nat.dvd_prime hp.out).mp (Nat.dvd_of_mod_eq_zero h0)
    omega
  subst p
  have hv (P : Ideal O) (hP : P ∈ primesOver 3) :
      Real.log (Ideal.absNorm P) = Real.log 3 := by
    have hPP := (mem_primesOver 3 P).mp hP
    let : P.IsPrime := hPP.1
    let : P.LiesOver (Ideal.span {(3 : ℤ)}) := hPP.2
    rw [ShortDraftHeckeBridge.absNorm_ramified P]
    norm_num
  rw [Finset.sum_congr rfl hv, Finset.sum_const, nsmul_eq_mul, primesOver_card]
  norm_num only [Nat.cast_ofNat]
  rw [ShortDraftHeckeBridge.ramified_count]
  norm_num only [Nat.cast_one, one_mul, Nat.cast_ofNat]
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

theorem coeff_prime_pow_le (p : ℕ) [hp : Fact p.Prime] {k : ℕ} (hk : 0 < k) :
    coeff (fun _ => 1) (p ^ k) ≤ 2 * Real.log p := by
  rw [coeff_eq_sum_primePowers]
  let S := (normFiber (p ^ k)).filter IsPrimePow
  have hS (I : Ideal O) (hI : I ∈ S) : IsPrimePow I ∧ Ideal.absNorm I = p ^ k :=
    ⟨(Finset.mem_filter.mp hI).2, (mem_normFiber _ I).mp (Finset.mem_filter.mp hI).1⟩
  have hinj : Set.InjOn primeBase (↑S : Set (Ideal O)) := by
    intro I hI J hJ heq
    exact primeBase_injective_on_norm (hS I hI).1 (hS J hJ).1
      ((hS I hI).2.trans (hS J hJ).2.symm) heq
  have hsub : S.image primeBase ⊆ primesOver p := by
    intro P hP
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hP
    exact (mem_primesOver p _).mpr (primeBase_mem_primesOver hp.out hk (hS I hI).1 (hS I hI).2)
  calc
    _ = ∑ P ∈ S.image primeBase, Real.log (Ideal.absNorm P) := (Finset.sum_image hinj).symm
    _ ≤ ∑ P ∈ primesOver p, Real.log (Ideal.absNorm P) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro P hP _
      have hPP := (mem_primesOver p P).mp hP
      have hprime : Prime P := Ideal.prime_of_mem_primesOver
        (by simpa using (show (p : ℤ) ≠ 0 by exact_mod_cast hp.out.ne_zero)) hPP
      exact Real.log_nonneg (by exact_mod_cast
        (SmoothMobiusCorrection.prime_norm_two_le ⟨P, hprime⟩).trans' (by decide : 1 ≤ 2))
    _ ≤ _ := primesOver_log_sum_le p

theorem coeff_le_two_vonMangoldt (w : Ideal O → ℝ) (hw : ∀ I, w I ≤ 1) (n : ℕ) :
    coeff w n ≤ 2 * vonMangoldt n := by
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    let : Fact p.Prime := ⟨hp⟩
    rw [vonMangoldt_apply_pow hk.ne', vonMangoldt_apply_prime hp]
    exact (coeff_le_unweighted w hw _).trans (coeff_prime_pow_le p hk)
  · rw [coeff_eq_zero_of_not_primePow hn, vonMangoldt_eq_zero_iff.mpr hn, mul_zero]

theorem coeff_chebyshev (w : Ideal O → ℝ) (hw0 : ∀ I, 0 ≤ w I)
    (hw1 : ∀ I, w I ≤ 1) :
    ∃ C : ℝ, ∀ N : ℕ, cumsum (fun n => ‖(coeff w n : ℂ)‖) N ≤ C * N := by
  obtain ⟨C, hC⟩ := vonMangoldt_cheby
  refine ⟨2 * C, fun N => ?_⟩
  calc
    _ ≤ 2 * cumsum (fun n => ‖(vonMangoldt n : ℂ)‖) N := by
      unfold cumsum
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (coeff_nonneg w hw0 n), abs_of_nonneg vonMangoldt_nonneg]
        using coeff_le_two_vonMangoldt w hw1 n
    _ ≤ 2 * (C * N) := mul_le_mul_of_nonneg_left (hC N) (by norm_num)
    _ = _ := by ring

theorem coeff_summable_nterm (w : Ideal O → ℝ) (hw0 : ∀ I, 0 ≤ w I)
    (hw1 : ∀ I, w I ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    Summable (nterm (fun n => (coeff w n : ℂ)) σ) := by
  have hs : Summable (nterm (fun n => (vonMangoldt n : ℂ)) σ) := by
    simpa only [← nterm_eq_norm_term] using
      (@ArithmeticFunction.LSeriesSummable_vonMangoldt (σ : ℂ) (by simpa using hσ)).norm
  apply (hs.mul_left 2).of_nonneg_of_le
  · intro n
    exact ite_nonneg (by positivity) (div_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _))
  · intro n
    by_cases hn : n = 0
    · simp only [nterm, hn, ite_true, mul_zero, le_refl]
    · simp only [nterm, hn, ite_false, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (coeff_nonneg w hw0 n), abs_of_nonneg vonMangoldt_nonneg]
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (coeff_le_two_vonMangoldt w hw1 n)
        (Real.rpow_nonneg (by positivity) _)

theorem coeff_LSeriesSummable (w : Ideal O → ℝ) (hw0 : ∀ I, 0 ≤ w I)
    (hw1 : ∀ I, w I ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (coeff w n : ℂ)) s := by
  apply Summable.of_norm
  simpa only [norm_term_eq_nterm_re] using coeff_summable_nterm w hw0 hw1 hs

def classCoeff (C : Set (Ideal O)) (n : ℕ) : ℝ :=
  coeff (fun I => if I ∈ C then 1 else 0) n

theorem classCoeff_nonneg (C : Set (Ideal O)) (n : ℕ) : 0 ≤ classCoeff C n :=
  coeff_nonneg _ (fun _ => by split_ifs <;> norm_num) n

theorem classCoeff_le_two_vonMangoldt (C : Set (Ideal O)) (n : ℕ) :
    classCoeff C n ≤ 2 * vonMangoldt n :=
  coeff_le_two_vonMangoldt _ (fun _ => by split_ifs <;> norm_num) n

theorem classCoeff_chebyshev (C : Set (Ideal O)) :
    ∃ B : ℝ, ∀ N : ℕ, cumsum (fun n => ‖(classCoeff C n : ℂ)‖) N ≤ B * N :=
  coeff_chebyshev _ (fun _ => by split_ifs <;> norm_num)
    (fun _ => by split_ifs <;> norm_num)

theorem classCoeff_summable_nterm (C : Set (Ideal O)) {σ : ℝ} (hσ : 1 < σ) :
    Summable (nterm (fun n => (classCoeff C n : ℂ)) σ) :=
  coeff_summable_nterm _ (fun _ => by split_ifs <;> norm_num)
    (fun _ => by split_ifs <;> norm_num) hσ

end

end SevenEighths.IdealMangoldt

end OAI

end Source469

/- Original source: OAI/NumberTheory/DirichletL/IdealLogDerivative.lean; sha256: aee9630303da5159e33828238d7ee8b76c4ebfa2b997ce1f762c182b314c0310 -/
section Source470
namespace OAI

namespace SevenEighths.IdealLogDerivative

open ActualEisensteinCubic UniqueFactorizationMonoid IdealEuler
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open scoped BigOperators Classical Topology

noncomputable section

def coeff (a : Ideal O →*₀ ℂ) (n : ℕ) : ℂ :=
  ShortDraftHeckeBridge.normFiberCoeff (fun I => (IdealMangoldt.value I : ℂ) * a I) n

theorem norm_coeff_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) (n : ℕ) :
    ‖coeff a n‖ ≤ IdealMangoldt.coeff (fun _ => 1) n := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (IdealMangoldt.value_nonneg I), one_mul]
  exact mul_le_of_le_one_right (IdealMangoldt.value_nonneg I) (ha I)

theorem norm_coeff_le_two_vonMangoldt (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (n : ℕ) :
    ‖coeff a n‖ ≤ 2 * ArithmeticFunction.vonMangoldt n :=
  (norm_coeff_le a ha n).trans
    (IdealMangoldt.coeff_le_two_vonMangoldt (fun _ => 1) (fun _ => le_refl _) n)

theorem coeff_summable (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : LSeriesSummable (coeff a) s := by
  apply Summable.of_norm
  have h := (IdealMangoldt.coeff_LSeriesSummable (fun _ => 1)
    (fun _ => zero_le_one) (fun _ => le_refl _) hs).norm
  apply h.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  apply LSeries.norm_term_le
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (IdealMangoldt.coeff_nonneg (fun _ => 1) (fun _ => zero_le_one) n)]
    using norm_coeff_le a ha n

theorem primePow_coprime_factor {B C : Ideal O} (h : IsPrimePow (B * C))
    (hBC : IsRelPrime B C) : B = 1 ∨ C = 1 := by
  obtain ⟨P, k, hP, hk, heq⟩ := h
  obtain ⟨i, hi, hBi⟩ := (dvd_prime_pow hP k).mp
    (heq.symm ▸ dvd_mul_right B C)
  obtain ⟨j, hj, hCj⟩ := (dvd_prime_pow hP k).mp
    (heq.symm ▸ dvd_mul_left C B)
  have hB := associated_iff_eq.mp hBi
  have hC := associated_iff_eq.mp hCj
  by_cases hi0 : i = 0
  · left; simpa only [hi0, pow_zero] using hB
  by_cases hj0 : j = 0
  · right; simpa only [hj0, pow_zero] using hC
  exact (hP.not_isUnit (hBC (hB ▸ dvd_pow_self P hi0) (hC ▸ dvd_pow_self P hj0))).elim

theorem value_mul_coprime {B C : Ideal O} (hBC : IsRelPrime B C) :
    IdealMangoldt.value (B * C) =
      (if C = 1 then IdealMangoldt.value B else 0) +
      (if B = 1 then IdealMangoldt.value C else 0) := by
  by_cases hB : B = 1
  · subst B
    simp only [one_mul, IdealMangoldt.value_one, ite_self, ite_true, zero_add]
  by_cases hC : C = 1
  · subst C
    simp only [mul_one, IdealMangoldt.value_one, ite_self, ite_true, add_zero]
  have hnot : ¬IsPrimePow (B * C) := by
    intro h
    exact (primePow_coprime_factor h hBC).elim hB hC
  simp only [IdealMangoldt.value, hnot, hB, hC, ite_false, zero_add]

theorem idealDivisors_one : idealDivisors (1 : Ideal O) = {1} := by
  ext D
  rw [mem_idealDivisors (show (1 : Ideal O) ≠ ⊥ from one_ne_zero), Finset.mem_singleton]
  exact isUnit_iff_dvd_one.symm.trans isUnit_iff_eq_one

theorem idealDivisors_prime_pow (P : Ideal O) (hP : Prime P) (k : ℕ) :
    idealDivisors (P ^ k) = (Finset.range (k + 1)).image (fun j => P ^ j) := by
  ext D
  rw [mem_idealDivisors (show P ^ k ≠ ⊥ from pow_ne_zero k hP.ne_zero), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨j, hj, hDj⟩ := (dvd_prime_pow hP k).mp hD
    exact ⟨j, Finset.mem_range.mpr (by omega), (associated_iff_eq.mp hDj).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact pow_dvd_pow P (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)

theorem sum_value_prime_pow (P : Ideal O) (hP : Prime P) (k : ℕ) :
    (∑ D ∈ idealDivisors (P ^ k), (IdealMangoldt.value D : ℂ)) =
      k * (Real.log (Ideal.absNorm P) : ℂ) := by
  rw [idealDivisors_prime_pow P hP k, Finset.sum_image]
  · induction k with
    | zero => simp only [Nat.zero_add, Finset.sum_range_one, pow_zero,
        IdealMangoldt.value_one, Complex.ofReal_zero, Nat.cast_zero, zero_mul]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, IdealMangoldt.value_pow hP (Nat.succ_pos k)]
      push_cast
      ring
  · exact fun i _ j _ hij => pow_injective_of_not_isUnit hP.not_isUnit hP.ne_zero hij

theorem sum_value_mul (B C : Ideal O) (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : IsRelPrime B C) :
    (∑ D ∈ idealDivisors (B * C), (IdealMangoldt.value D : ℂ)) =
      (∑ D ∈ idealDivisors B, (IdealMangoldt.value D : ℂ)) +
      ∑ D ∈ idealDivisors C, (IdealMangoldt.value D : ℂ) := by
  have hcop : IsCoprime B C := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply Ideal.isUnit_iff.mp
    exact hBC (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right)
  have h1B : (1 : Ideal O) ∈ idealDivisors B := (mem_idealDivisors hB).mpr (one_dvd _)
  have h1C : (1 : Ideal O) ∈ idealDivisors C := (mem_idealDivisors hC).mpr (one_dvd _)
  rw [QuadraticDivisorSplit.sum_divisors_coprime_product B C hB hC hcop]
  calc
    _ = ∑ D ∈ idealDivisors B, ∑ E ∈ idealDivisors C,
        ((if E = 1 then (IdealMangoldt.value D : ℂ) else 0) +
        (if D = 1 then (IdealMangoldt.value E : ℂ) else 0)) := by
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro E hE
      rw [value_mul_coprime ((hBC.of_dvd_left ((mem_idealDivisors hB).mp hD)).of_dvd_right
        ((mem_idealDivisors hC).mp hE)), Complex.ofReal_add]
      split_ifs <;> rfl
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_irrel,
        Finset.sum_ite_eq', ite_eq_left h1C, ite_eq_left h1B, Finset.sum_const_zero]

theorem sum_value_divisors (B : Ideal O) (hB : B ≠ 0) :
    (∑ D ∈ idealDivisors B, (IdealMangoldt.value D : ℂ)) =
      (Real.log (Ideal.absNorm B) : ℂ) := by
  induction B using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => exact (hB rfl).elim
  | h1 hunit =>
    rw [isUnit_iff_eq_one.mp hunit, idealDivisors_one, Finset.sum_singleton]
    simp only [IdealMangoldt.value_one, map_one, Nat.cast_one, Real.log_one]
  | hpr k hP =>
    rw [sum_value_prime_pow _ hP k, map_pow, Nat.cast_pow, Real.log_pow]
    push_cast
    rfl
  | @hcp B C hBC ihB ihC =>
    have hB0 : B ≠ 0 := left_ne_zero_of_mul hB
    have hC0 : C ≠ 0 := right_ne_zero_of_mul hB
    rw [sum_value_mul B C hB0 hC0 hBC, ihB hB0, ihC hC0, map_mul, Nat.cast_mul,
      Real.log_mul (by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hB0))
        (by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hC0)), Complex.ofReal_add]

theorem value_le_log_norm (B : Ideal O) :
    IdealMangoldt.value B ≤ Real.log (Ideal.absNorm B) := by
  by_cases h : IsPrimePow B
  · obtain ⟨P, k, hP, hk, rfl⟩ := h
    rw [IdealMangoldt.value_pow hP hk, map_pow, Nat.cast_pow, Real.log_pow]
    apply le_mul_of_one_le_left
    · exact Real.log_natCast_nonneg _
    · exact_mod_cast hk
  · rw [IdealMangoldt.value, ite_eq_right h]
    exact Real.log_natCast_nonneg _

theorem weighted_eq_term (a : Ideal O →*₀ ℂ) (s : ℂ) (B : Ideal O) :
    weighted a s B = LSeries.term (fun _ => a B) s (Ideal.absNorm B) := by
  by_cases hB : B = 0
  · subst B
    simp only [map_zero, LSeries.term_zero]
  · have hn : Ideal.absNorm B ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hB
    change a B * CubicEisenstein.fullIdealWeight s B = _
    simp only [CubicEisenstein.fullIdealWeight, hB, ite_false,
      LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]

theorem weighted_hasDerivAt (a : Ideal O →*₀ ℂ) (s : ℂ) (B : Ideal O) :
    HasDerivAt (fun z => weighted a z B)
      (-((Real.log (Ideal.absNorm B) : ℂ) * weighted a s B)) s := by
  simp_rw [weighted_eq_term]
  convert LSeries.hasDerivAt_term (fun _ => a B) (Ideal.absNorm B) s using 1
  by_cases hn : Ideal.absNorm B = 0
  · simp only [hn, LSeries.term_zero, mul_zero]
  · simp only [LSeries.term_of_ne_zero hn, LSeries.logMul, Complex.natCast_log,
      mul_div_assoc]

theorem log_weighted_hasSum (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun B : Ideal O => (Real.log (Ideal.absNorm B) : ℂ) * weighted a s B)
      (-deriv (series a) s) := by
  obtain ⟨x, hx, hxs⟩ := exists_between hs
  have hu := weighted_summable_norm a ha (x : ℂ) (by simpa using hx)
  have hd (B : Ideal O) : DifferentiableOn ℂ (fun z => weighted a z B) {z : ℂ | x < z.re} :=
    fun z _ => (weighted_hasDerivAt a z B).differentiableAt.differentiableWithinAt
  have hU : IsOpen {z : ℂ | x < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hbound (B : Ideal O) (z : ℂ) (hz : z ∈ {z : ℂ | x < z.re}) :
      ‖weighted a z B‖ ≤ ‖weighted a (x : ℂ) B‖ := by
    simp only [weighted_eq_term]
    exact LSeries.norm_term_le_of_re_le_re _ (by simpa using hz.le) _
  have H := Complex.hasSum_deriv_of_summable_norm hu hd hU hbound hxs
  simp_rw [(weighted_hasDerivAt a s _).deriv] at H
  unfold IdealEuler.series
  simpa only [neg_neg] using H.neg

theorem mangoldt_weighted_summable_norm (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun B : Ideal O => ‖(IdealMangoldt.value B : ℂ) * weighted a s B‖) := by
  apply (log_weighted_hasSum a ha s hs).summable.norm.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro B
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (IdealMangoldt.value_nonneg B), abs_of_nonneg (Real.log_natCast_nonneg _)]
  exact mul_le_mul_of_nonneg_right (value_le_log_norm B) (norm_nonneg _)

theorem mangoldt_series_eq_LSeries (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    (∑' B : Ideal O, (IdealMangoldt.value B : ℂ) * weighted a s B) = LSeries (coeff a) s := by
  have H := (mangoldt_weighted_summable_norm a ha s hs).of_norm.hasSum.tsum_fiberwise Ideal.absNorm
  change HasSum (fun n : ℕ => ∑' B : {B : Ideal O // Ideal.absNorm B = n},
    (IdealMangoldt.value B.val : ℂ) * weighted a s B.val) _ at H
  have hf (n : ℕ) : (∑' B : {B : Ideal O // Ideal.absNorm B = n},
      (IdealMangoldt.value B.val : ℂ) * weighted a s B.val) = LSeries.term (coeff a) s n := by
    unfold coeff
    simpa only [weighted, normWeight,
      MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, mul_assoc]
      using SmoothMobiusCorrection.idealDirichlet_fiber
        (fun B => (IdealMangoldt.value B : ℂ) * a B) s n
  simp_rw [hf] at H
  exact H.tsum_eq.symm

theorem mulFiber_value_sum (B : Ideal O) (hB : B ≠ 0) :
    (∑' p : CompletedGauss.MulFiber B, (IdealMangoldt.value p.val.1 : ℂ)) =
      (Real.log (Ideal.absNorm B) : ℂ) := by
  let e := CompletedGauss.mulFiberDivisorEquiv B hB
  calc
    _ = ∑' D : {D : Ideal O // D ∈ idealDivisors B}, (IdealMangoldt.value D.val : ℂ) :=
      e.tsum_eq (fun D => (IdealMangoldt.value D.val : ℂ))
    _ = ∑ D ∈ idealDivisors B, (IdealMangoldt.value D : ℂ) := by
      rw [tsum_fintype]
      exact (Finset.sum_subtype (idealDivisors B) (fun _ => Iff.rfl)
        (fun D => (IdealMangoldt.value D : ℂ))).symm
    _ = _ := sum_value_divisors B hB

theorem coeff_LSeries_mul_series (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    LSeries (coeff a) s * series a s = -deriv (series a) s := by
  let f := weighted a s
  let F : Ideal O × Ideal O → ℂ := fun p => (IdealMangoldt.value p.1 : ℂ) * f (p.1 * p.2)
  have hprod := (mangoldt_weighted_summable_norm a ha s hs).mul_norm
    (weighted_summable_norm a ha s hs)
  have hF : Summable F := by
    apply hprod.of_norm.congr
    intro p
    dsimp only [F, f]
    rw [map_mul]
    ring
  have hfiber (B : Ideal O) : (∑' p : CompletedGauss.MulFiber B, F p.val) =
      (Real.log (Ideal.absNorm B) : ℂ) * f B := by
    by_cases hB : B = 0
    · subst B
      have hz (p : CompletedGauss.MulFiber 0) : F p.val = 0 := by
        simp only [F, p.property, map_zero, mul_zero]
      simp only [hz, tsum_zero, map_zero, mul_zero]
    · calc
        _ = (∑' p : CompletedGauss.MulFiber B, (IdealMangoldt.value p.val.1 : ℂ)) * f B := by
          rw [← tsum_mul_right]
          exact tsum_congr (fun p => by simp only [F, p.property])
        _ = _ := by rw [mulFiber_value_sum B hB]
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1 * p.2)
  change HasSum (fun B : Ideal O => ∑' p : CompletedGauss.MulFiber B, F p.val) _ at hsum
  simp_rw [hfiber] at hsum
  calc
    _ = (∑' B : Ideal O, (IdealMangoldt.value B : ℂ) * f B) * ∑' B : Ideal O, f B := by
      rw [mangoldt_series_eq_LSeries a ha s hs]
      rfl
    _ = ∑' p : Ideal O × Ideal O, ((IdealMangoldt.value p.1 : ℂ) * f p.1) * f p.2 :=
      tsum_mul_tsum_of_summable_norm (mangoldt_weighted_summable_norm a ha s hs)
        (weighted_summable_norm a ha s hs)
    _ = ∑' p, F p := by
      apply tsum_congr
      intro p
      simp only [F, map_mul]
      ring
    _ = -deriv (series a) s := hsum.unique (log_weighted_hasSum a ha s hs)

theorem coeff_LSeries_eq_neg_logDeriv (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    LSeries (coeff a) s = -deriv (series a) s / series a s := by
  apply (eq_div_iff (series_ne_zero a ha s hs)).mpr
  exact coeff_LSeries_mul_series a ha s hs

theorem coeff_LSeries_eq_neg_logDeriv_of_eq (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 1 < z.re → F z = series a z)
    (s : ℂ) (hs : 1 < s.re) :
    LSeries (coeff a) s = -deriv F s / F s := by
  have hd : deriv F s = deriv (series a) s := by
    apply Filter.EventuallyEq.deriv_eq
    have hU : {z : ℂ | 1 < z.re} ∈ nhds s :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
    filter_upwards [hU] with z hz
    exact hF z hz
  rw [hd, hF s hs]
  exact coeff_LSeries_eq_neg_logDeriv a ha s hs

end
end SevenEighths.IdealLogDerivative

end OAI

end Source470

/- Original source: OAI/NumberTheory/DirichletL/Hecke/LogDerivative.lean; sha256: fe1c9db01e5dd1db995f6bcc1af25598df6a3e1a33cc44a4683e349a709f663f -/
section Source471
namespace OAI

noncomputable section
open scoped Classical Topology
namespace SevenEighths.HeckeLogDerivative
open HeckeFamily

def coeff (χ : Character) : ℕ → ℂ := IdealLogDerivative.coeff (idealCoeff χ)

theorem coeff_LSeries_eq (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LSeries (coeff χ) s = -deriv (LFunction χ) s / LFunction χ s :=
  IdealLogDerivative.coeff_LSeries_eq_neg_logDeriv_of_eq _ (idealCoeff_norm_le_one χ)
    (LFunction χ) (fun _ hz => LFunction_eq_series χ hz) s hs

def poleSubtracted (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue = 1 then
    -deriv (HeckeOrigin.poleRemoved χ) s / HeckeOrigin.poleRemoved χ s
  else -deriv (LFunction χ) s / LFunction χ s

theorem poleRemoved_ne_zero_boundary (χ : Character) (hχ : χ.residue = 1)
    {s : ℂ} (hs : 1 ≤ s.re) : HeckeOrigin.poleRemoved χ s ≠ 0 := by
  by_cases h1 : s = 1
  · subst s
    exact HeckeOrigin.poleRemoved_one_ne_zero χ hχ
  · rw [HeckeOrigin.poleRemoved_eq χ (by intro h; norm_num [h] at hs) h1]
    exact mul_ne_zero (sub_ne_zero.mpr h1) (LFunction_ne_zero_of_one_le_re χ hs (Or.inl h1))

theorem poleSubtracted_analyticAt (χ : Character) {s : ℂ} (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (poleSubtracted χ) s := by
  by_cases hχ : χ.residue = 1
  · have heq : poleSubtracted χ = fun z =>
        -deriv (HeckeOrigin.poleRemoved χ) z / HeckeOrigin.poleRemoved χ z := by
      funext z
      simp [poleSubtracted, hχ]
    rw [heq]
    have ha := (HeckeOrigin.poleRemoved_entire χ).analyticAt s
    exact ha.deriv.neg.div ha (poleRemoved_ne_zero_boundary χ hχ hs)
  · have heq : poleSubtracted χ = fun z => -deriv (LFunction χ) z / LFunction χ z := by
      funext z
      simp [poleSubtracted, hχ]
    rw [heq]
    have ha := (LFunction_entire_nonprincipal χ hχ).analyticAt s
    exact ha.deriv.neg.div ha (LFunction_ne_zero_of_one_le_re χ hs (Or.inr hχ))

theorem poleSubtracted_continuousOn (χ : Character) :
    ContinuousOn (poleSubtracted χ) {s : ℂ | 1 ≤ s.re} :=
  fun _ hs => (poleSubtracted_analyticAt χ hs).continuousAt.continuousWithinAt

theorem poleRemoved_deriv (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    deriv (HeckeOrigin.poleRemoved χ) s = LFunction χ s + (s-1)*deriv (LFunction χ) s := by
  have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
  have heq : HeckeOrigin.poleRemoved χ =ᶠ[nhds s] (fun z => (z-1)*LFunction χ z) := by
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds hs] with z hz
    exact HeckeOrigin.poleRemoved_eq χ
      (by intro h; norm_num [h] at hz) (by intro h; norm_num [h] at hz)
  rw [heq.deriv_eq]
  have hd := (LFunction_differentiableAt χ h0 (Or.inl h1)).hasDerivAt
  have hh := ((hasDerivAt_id s).sub_const 1 |>.mul hd).deriv
  have hfun : ((fun x : ℂ => id x - 1) * LFunction χ) =
      (fun z => (z-1)*LFunction χ z) := rfl
  rw [hfun] at hh
  simpa only [one_mul, id_eq] using hh

theorem coeff_LSeries_eq_poleSubtracted (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LSeries (coeff χ) s = (if χ.residue = 1 then (1 : ℂ)/(s-1) else 0) +
      poleSubtracted χ s := by
  rw [coeff_LSeries_eq χ hs]
  by_cases hχ : χ.residue = 1
  · simp only [hχ, ite_true, poleSubtracted]
    have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
    have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
    rw [poleRemoved_deriv χ hs, HeckeOrigin.poleRemoved_eq χ h0 h1]
    have hn := LFunction_ne_zero_of_one_lt_re χ hs
    field_simp
    ; ring
  · simp [poleSubtracted, hχ]

end SevenEighths.HeckeLogDerivative

end

end OAI

end Source471

/- Original source: OAI/NumberTheory/DirichletL/Hecke/RayFamily.lean; sha256: 86c80381f402618d744802694f1f09a9ab6a197d8730bcdd50d99a646c871c7e -/
section Source472
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeRayFamily
open HeckeFamily

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

def character (χ : RayOrthogonality.rayCharacters M) : Character :=
  Character.ofResidue M (NeZero.ne M) χ.val ((RayOrthogonality.mem_rayCharacters_iff M χ.val).mp χ.property)

theorem idealCoeff_character (χ : RayOrthogonality.rayCharacters M) (I : Ideal O) :
    idealCoeff (character M χ) I = RayOrthogonality.idealCharacter M χ I := rfl

theorem principal_iff (χ : RayOrthogonality.rayCharacters M) :
    (character M χ).residue = 1 ↔ χ = 1 := by
  change χ.val = 1 ↔ χ = 1
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem character_entire (χ : RayOrthogonality.rayCharacters M) (hχ : χ ≠ 1) :
    Differentiable ℂ (LFunction (character M χ)) :=
  LFunction_entire_nonprincipal _ (fun h => hχ ((principal_iff M χ).mp h))

theorem character_boundary_ne_zero (χ : RayOrthogonality.rayCharacters M)
    {s : ℂ} (hs : 1 ≤ s.re) (hpole : s ≠ 1 ∨ χ ≠ 1) :
    LFunction (character M χ) s ≠ 0 := by
  apply LFunction_ne_zero_of_one_le_re _ hs
  exact hpole.imp id (fun h hn => h ((principal_iff M χ).mp hn))

theorem principal_pole_ne_zero : HeckeOrigin.poleRemoved (character M 1) 1 ≠ 0 :=
  HeckeOrigin.poleRemoved_one_ne_zero _ rfl

theorem average_idealCoeff (I : Ideal O) :
    (RayOrthogonality.rayCard M : ℂ)⁻¹ *
      ∑ χ : RayOrthogonality.rayCharacters M, idealCoeff (character M χ) I =
      if I ∈ RayOrthogonality.principalIdeals M then 1 else 0 := by
  simp only [idealCoeff_character]
  simpa only [div_eq_mul_inv, mul_comm] using RayOrthogonality.average_idealCharacters M I

theorem mangoldt_LSeries (χ : RayOrthogonality.rayCharacters M)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (IdealLogDerivative.coeff (RayOrthogonality.idealCharacter M χ)) s =
      (if χ = 1 then (1 : ℂ)/(s-1) else 0) +
        HeckeLogDerivative.poleSubtracted (character M χ) s := by
  have h := HeckeLogDerivative.coeff_LSeries_eq_poleSubtracted (character M χ) hs
  change LSeries (IdealLogDerivative.coeff (idealCoeff (character M χ))) s = _ at h
  have heq : idealCoeff (character M χ) = RayOrthogonality.idealCharacter M χ := rfl
  rw [heq, principal_iff] at h
  by_cases hc : χ = 1 <;> simpa [hc] using h

theorem poleSubtracted_analyticAt (χ : RayOrthogonality.rayCharacters M)
    {s : ℂ} (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (HeckeLogDerivative.poleSubtracted (character M χ)) s :=
  HeckeLogDerivative.poleSubtracted_analyticAt _ hs

end SevenEighths.HeckeRayFamily

end

end OAI

end Source472

/- Original source: OAI/NumberTheory/DirichletL/RayQuotient.lean; sha256: 250f6013c7423bbfaf24bc4e6b7d5a3b99a10b48115c0d5f05eb5e4a3cd6af14 -/
section Source473
namespace OAI

namespace SevenEighths.RayQuotient
open SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section

variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]
    (H : Subgroup (A ⧸ M)ˣ) (hH : globalUnits M ≤ H)

abbrev Characters := characters H
abbrev classNumber := Nat.card ((A ⧸ M)ˣ ⧸ H)

theorem classNumber_pos : 0 < classNumber M H := ray_card_pos H

include hH

theorem character_unitInvariant (χ : Characters M H) :
    IdealCharacter.UnitInvariant M χ := by
  intro u
  exact (mem_characters_iff H χ).mp χ.property _ (hH ⟨u, rfl⟩)

def toFullRay : Characters M H →* rayCharacters M where
  toFun χ := ⟨χ, (mem_rayCharacters_iff M χ).mpr (character_unitInvariant M H hH χ)⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem toFullRay_injective : Function.Injective (toFullRay M H hH) := by
  intro χ ψ heq
  exact Subtype.ext (congrArg (fun ρ : rayCharacters M => (ρ : MulChar (A ⧸ M) ℂ)) heq)

@[simp] theorem toFullRay_eq_one (χ : Characters M H) :
    toFullRay M H hH χ = 1 ↔ χ = 1 := by
  rw [← map_one (toFullRay M H hH)]
  exact (toFullRay_injective M H hH).eq_iff

variable [IsDomain A] [IsPrincipalIdealRing A]

def idealCharacter (χ : Characters M H) : Ideal A →*₀ ℂ :=
  IdealCharacter.ofResidue M χ (character_unitInvariant M H hH χ)

theorem idealCharacter_eq_fullRay (χ : Characters M H) :
    idealCharacter M H hH χ = RayOrthogonality.idealCharacter M (toFullRay M H hH χ) := rfl

def identityClass : Set (Ideal A) :=
  {I | I ≠ ⊥ ∧ ∃ a : A, Ideal.span ({a} : Set A) = I ∧
    inUnitSubgroup H (Ideal.Quotient.mk M a)}

omit [Finite (A ⧸ M)] in
theorem identityClass_iff_generator {I : Ideal A} (hI : I ≠ ⊥) :
    I ∈ identityClass M H ↔
      inUnitSubgroup H (Ideal.Quotient.mk M (Submodule.IsPrincipal.generator I)) := by
  constructor
  · rintro ⟨_, a, ha, u, hua, huH⟩
    have hga : Associated (Submodule.IsPrincipal.generator I) a := by
      rw [← ha]
      exact Submodule.IsPrincipal.associated_generator_span_self a
    obtain ⟨v, hv⟩ := hga
    let w := Units.map (Ideal.Quotient.mk M).toMonoidHom v
    refine ⟨u * w⁻¹, ?_, H.mul_mem huH (H.inv_mem (hH ⟨v, rfl⟩))⟩
    have hq := congrArg (Ideal.Quotient.mk M) hv
    simp only [map_mul] at hq
    change (u : A ⧸ M) * ((Units.map (Ideal.Quotient.mk M).toMonoidHom v)⁻¹ :
      (A ⧸ M)ˣ) = _
    rw [hua, ← hq]
    change (Ideal.Quotient.mk M (Submodule.IsPrincipal.generator I)) *
      (w : A ⧸ M) * (w⁻¹ : (A ⧸ M)ˣ) = _
    rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  · intro h
    exact ⟨hI, _, Ideal.span_singleton_generator I, h⟩

theorem norm_idealCharacter_le_one (χ : Characters M H) (I : Ideal A) :
    ‖idealCharacter M H hH χ I‖ ≤ 1 :=
  IdealCharacter.norm_ofResidue_le_one M χ _ I

theorem idealCharacter_one (I : Ideal A) :
    idealCharacter M H hH 1 I =
      if I = ⊥ then 0 else if IsCoprime I M then 1 else 0 :=
  IdealCharacter.ofResidue_one M I

theorem sum_idealCharacters (I : Ideal A) :
    ∑ χ : Characters M H, idealCharacter M H hH χ I =
      if I ∈ identityClass M H then (classNumber M H : ℂ) else 0 := by
  by_cases hI : I = ⊥
  · subst I
    simp [idealCharacter, identityClass]
  · have heq (χ : Characters M H) : idealCharacter M H hH χ I =
        (χ : MulChar (A ⧸ M) ℂ) (Ideal.Quotient.mk M (Submodule.IsPrincipal.generator I)) := by
      exact IdealCharacter.ofResidue_of_generator M χ _ hI (Ideal.span_singleton_generator I)
    simp only [heq, sum_characters, identityClass_iff_generator M H hH hI, classNumber]

theorem average_idealCharacters (I : Ideal A) :
    (∑ χ : Characters M H, idealCharacter M H hH χ I) / (classNumber M H : ℂ) =
      if I ∈ identityClass M H then 1 else 0 := by
  rw [sum_idealCharacters]
  have hn : (classNumber M H : ℂ) ≠ 0 := by exact_mod_cast (classNumber_pos M H).ne'
  split_ifs <;> simp [hn]

omit [Finite (A ⧸ M)] [IsPrincipalIdealRing A] [IsDomain A] hH in
theorem identityClass_globalUnits : identityClass M (globalUnits M) = principalIdeals M := by
  ext I
  simp only [identityClass, principalIdeals, Set.mem_ofPred_eq,
    inUnitSubgroup_globalUnits_iff]

end
end SevenEighths.RayQuotient

end OAI

end Source473

/- Original source: OAI/NumberTheory/DirichletL/PrimeCounting/RayAsymptotic.lean; sha256: c94d064e68a68ab49e211d5f077e79c4ea6fe3cd2fb9193240a06acb99afd22b -/
section Source474
namespace OAI

namespace SevenEighths.PNT.RayAsymptotic

open ActualEisensteinCubic RayOrthogonality Filter
open scoped BigOperators Classical Topology

noncomputable section

variable (M : Ideal O) [Finite (O ⧸ M)]

def classCoeff (n : ℕ) : ℝ := IdealMangoldt.classCoeff (principalIdeals M) n

theorem sum_coeff (n : ℕ) :
    (∑ χ : rayCharacters M, IdealLogDerivative.coeff (idealCharacter M χ) n) =
      (rayCard M : ℂ) * (classCoeff M n : ℂ) := by
  unfold IdealLogDerivative.coeff ShortDraftHeckeBridge.normFiberCoeff
  rw [Finset.sum_comm]
  unfold classCoeff IdealMangoldt.classCoeff IdealMangoldt.coeff IdealMangoldt.normFiber
  rw [Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [← Finset.mul_sum, sum_idealCharacters]
  by_cases hI : I ∈ principalIdeals M
  · simp only [hI, ite_true, one_mul, mul_comm]
  · simp only [hI, ite_false, zero_mul, Complex.ofReal_zero, mul_zero]

theorem average_coeff (n : ℕ) :
    (classCoeff M n : ℂ) =
      (∑ χ : rayCharacters M, IdealLogDerivative.coeff (idealCharacter M χ) n) /
        (rayCard M : ℂ) := by
  rw [sum_coeff]
  have hc : (rayCard M : ℂ) ≠ 0 := by exact_mod_cast (rayCard_pos M).ne'
  exact (mul_div_cancel_left₀ _ hc).symm

theorem classCoeff_LSeries (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => (classCoeff M n : ℂ)) s =
      (∑ χ : rayCharacters M, LSeries (IdealLogDerivative.coeff (idealCharacter M χ)) s) /
        (rayCard M : ℂ) := by
  have heq : (fun n => (classCoeff M n : ℂ)) =
      (rayCard M : ℂ)⁻¹ • ∑ χ : rayCharacters M, IdealLogDerivative.coeff (idealCharacter M χ) := by
    funext n
    rw [average_coeff]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq, LSeries_smul, LSeries_sum]
  · rw [div_eq_mul_inv, mul_comm]
  · intro χ _
    exact IdealLogDerivative.coeff_summable _ (norm_idealCharacter_le_one M χ) s hs

def principalRegularization (F : ℂ → ℂ) (residue : ℂ) : ℂ → ℂ :=
  Function.update (fun s => (s - 1) * F s) 1 residue

omit [Finite (O ⧸ M)] in
theorem principalRegularization_eventuallyEq (F : ℂ → ℂ) (residue : ℂ)
    {s : ℂ} (hs : s ≠ 1) :
    principalRegularization F residue =ᶠ[𝓝 s] (fun z => (z - 1) * F z) := by
  refine eventuallyEq_iff_exists_mem.mpr ?_
  exact ⟨_, isOpen_ne.mem_nhds hs, fun z hz => Function.update_of_ne (Set.mem_ofPred.mp hz) ..⟩

omit [Finite (O ⧸ M)] in
theorem principalRegularization_analyticAt (F : ℂ → ℂ) (residue : ℂ)
    {s : ℂ} (hs : s ≠ 1) (hF : AnalyticAt ℂ F s) :
    AnalyticAt ℂ (principalRegularization F residue) s :=
  ((analyticAt_id.sub analyticAt_const).mul hF).congr
    (principalRegularization_eventuallyEq F residue hs).symm

omit [Finite (O ⧸ M)] in

theorem principalRegularization_analyticAt_of_local (F R : ℂ → ℂ)
    (hR : AnalyticAt ℂ R 1)
    (hFR : ∀ᶠ s in 𝓝 (1 : ℂ), s ≠ 1 → (s - 1) * F s = R s) :
    AnalyticAt ℂ (principalRegularization F (R 1)) 1 := by
  apply hR.congr
  filter_upwards [hFR] with s hs
  by_cases hs1 : s = 1
  · subst s
    simp only [principalRegularization, Function.update_self]
  · rw [principalRegularization, Function.update_of_ne hs1]
    exact (hs hs1).symm

omit [Finite (O ⧸ M)] in
theorem principalRegularization_logDeriv (F : ℂ → ℂ) (residue : ℂ)
    {s : ℂ} (hs : s ≠ 1) (hF : AnalyticAt ℂ F s) (hF0 : F s ≠ 0) :
    -deriv (principalRegularization F residue) s / principalRegularization F residue s =
      -deriv F s / F s - 1 / (s - 1) := by
  have hd := (principalRegularization_eventuallyEq F residue hs).deriv_eq
  rw [hd, principalRegularization, Function.update_of_ne hs,
    deriv_fun_mul (by fun_prop) hF.differentiableAt, deriv_sub_const, deriv_id'', one_mul]
  field_simp
  ring

def regularizedFamily (F : rayCharacters M → ℂ → ℂ) (residue : ℂ)
    (χ : rayCharacters M) : ℂ → ℂ :=
  if χ = 1 then principalRegularization (F χ) residue else F χ

def remainder (F : rayCharacters M → ℂ → ℂ) (residue : ℂ) (s : ℂ) : ℂ :=
  (∑ χ : rayCharacters M,
    -deriv (regularizedFamily M F residue χ) s / regularizedFamily M F residue χ s) /
      (rayCard M : ℂ)

structure AnalyticFamily (F : rayCharacters M → ℂ → ℂ) (residue : ℂ) : Prop where
  eq_series : ∀ (χ : rayCharacters M) (s : ℂ), 1 < s.re →
    F χ s = IdealEuler.series (idealCharacter M χ) s
  analytic : ∀ (χ : rayCharacters M) (s : ℂ), 1 ≤ s.re →
    χ ≠ 1 ∨ s ≠ 1 → AnalyticAt ℂ (F χ) s
  nonzero : ∀ (χ : rayCharacters M) (s : ℂ), 1 ≤ s.re →
    χ ≠ 1 ∨ s ≠ 1 → F χ s ≠ 0
  pole_analytic : AnalyticAt ℂ (principalRegularization (F 1) residue) 1
  residue_ne_zero : residue ≠ 0

theorem regularizedFamily_analyticAt {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) (χ : rayCharacters M) (s : ℂ) (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (regularizedFamily M F residue χ) s := by
  by_cases hχ : χ = 1
  · subst χ
    rw [regularizedFamily, ite_eq_left rfl]
    by_cases hs1 : s = 1
    · subst s
      exact hF.pole_analytic
    · exact principalRegularization_analyticAt _ _ hs1 (hF.analytic 1 s hs (Or.inr hs1))
  · rw [regularizedFamily, ite_eq_right hχ]
    exact hF.analytic χ s hs (Or.inl hχ)

theorem regularizedFamily_ne_zero {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) (χ : rayCharacters M) (s : ℂ) (hs : 1 ≤ s.re) :
    regularizedFamily M F residue χ s ≠ 0 := by
  by_cases hχ : χ = 1
  · subst χ
    rw [regularizedFamily, ite_eq_left rfl]
    by_cases hs1 : s = 1
    · subst s
      simpa only [principalRegularization, Function.update_self] using hF.residue_ne_zero
    · rw [principalRegularization, Function.update_of_ne hs1]
      exact mul_ne_zero (sub_ne_zero.mpr hs1) (hF.nonzero 1 s hs (Or.inr hs1))
  · rw [regularizedFamily, ite_eq_right hχ]
    exact hF.nonzero χ s hs (Or.inl hχ)

theorem remainder_continuousOn {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) :
    ContinuousOn (remainder M F residue) {s : ℂ | 1 ≤ s.re} := by
  intro s hs
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div_const
  apply tendsto_finsetSum
  intro χ _
  have h := regularizedFamily_analyticAt M hF χ s hs
  exact h.deriv.continuousAt.neg.div h.continuousAt (regularizedFamily_ne_zero M hF χ s hs)

theorem regularizedFamily_logDeriv {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) (χ : rayCharacters M) (s : ℂ) (hs : 1 < s.re) :
    -deriv (regularizedFamily M F residue χ) s / regularizedFamily M F residue χ s =
      -deriv (F χ) s / F χ s - (if χ = 1 then 1 / (s - 1) else 0) := by
  by_cases hχ : χ = 1
  · rw [regularizedFamily, ite_eq_left hχ, ite_eq_left hχ]
    have hs1 : s ≠ 1 := by intro heq; simp only [heq, Complex.one_re] at hs; linarith
    exact principalRegularization_logDeriv _ _ hs1
      (hF.analytic χ s hs.le (Or.inr hs1)) (hF.nonzero χ s hs.le (Or.inr hs1))
  · simp only [regularizedFamily, hχ, ite_false, sub_zero]

theorem remainder_eqOn {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) :
    Set.EqOn (remainder M F residue)
      (fun s => LSeries (fun n => (classCoeff M n : ℂ)) s -
        (rayCard M : ℂ)⁻¹ / (s - 1)) {s : ℂ | 1 < s.re} := by
  intro s hs
  change remainder M F residue s = LSeries (fun n => (classCoeff M n : ℂ)) s -
    (rayCard M : ℂ)⁻¹ / (s - 1)
  rw [remainder, classCoeff_LSeries M s hs]
  simp_rw [regularizedFamily_logDeriv M hF _ s hs]
  rw [Finset.sum_sub_distrib]
  have hsum : (∑ χ : rayCharacters M, if χ = 1 then 1 / (s - 1) else (0 : ℂ)) =
      1 / (s - 1) := by simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hsum]
  have hlog (χ : rayCharacters M) : -deriv (F χ) s / F χ s =
      LSeries (IdealLogDerivative.coeff (idealCharacter M χ)) s :=
    (IdealLogDerivative.coeff_LSeries_eq_neg_logDeriv_of_eq _
      (norm_idealCharacter_le_one M χ) (F χ) (hF.eq_series χ) s hs).symm
  simp_rw [hlog]
  ring

theorem classCoeff_ratio_tendsto {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) :
    Tendsto (fun N : ℕ => cumsum (classCoeff M) N / N)
      atTop (𝓝 ((rayCard M : ℝ)⁻¹)) := by
  apply WienerIkeharaTheorem'
    (IdealMangoldt.classCoeff_nonneg (principalIdeals M))
    (fun σ hσ => IdealMangoldt.classCoeff_summable_nterm (principalIdeals M) hσ)
    (IdealMangoldt.classCoeff_chebyshev (principalIdeals M))
    (remainder_continuousOn M hF)
  simpa only [classCoeff, Complex.ofReal_inv, Complex.ofReal_natCast] using remainder_eqOn M hF

section Quotient

variable (H : Subgroup (O ⧸ M)ˣ) (hH : globalUnits M ≤ H)

def quotientClassCoeff (n : ℕ) : ℝ := IdealMangoldt.classCoeff (RayQuotient.identityClass M H) n

theorem quotient_sum_coeff (n : ℕ) :
    (∑ χ : RayQuotient.Characters M H,
      IdealLogDerivative.coeff (RayQuotient.idealCharacter M H hH χ) n) =
      (RayQuotient.classNumber M H : ℂ) * (quotientClassCoeff M H n : ℂ) := by
  unfold IdealLogDerivative.coeff ShortDraftHeckeBridge.normFiberCoeff
  rw [Finset.sum_comm]
  unfold quotientClassCoeff IdealMangoldt.classCoeff IdealMangoldt.coeff IdealMangoldt.normFiber
  rw [Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [← Finset.mul_sum, RayQuotient.sum_idealCharacters]
  by_cases hI : I ∈ RayQuotient.identityClass M H
  · simp only [hI, ite_true, one_mul, mul_comm]
  · simp only [hI, ite_false, zero_mul, Complex.ofReal_zero, mul_zero]

theorem quotient_average_coeff (n : ℕ) :
    (quotientClassCoeff M H n : ℂ) =
      (∑ χ : RayQuotient.Characters M H,
        IdealLogDerivative.coeff (RayQuotient.idealCharacter M H hH χ) n) /
          (RayQuotient.classNumber M H : ℂ) := by
  rw [quotient_sum_coeff]
  have hc : (RayQuotient.classNumber M H : ℂ) ≠ 0 := by
    exact_mod_cast (RayQuotient.classNumber_pos M H).ne'
  exact (mul_div_cancel_left₀ _ hc).symm

theorem quotientClassCoeff_LSeries (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => (quotientClassCoeff M H n : ℂ)) s =
      (∑ χ : RayQuotient.Characters M H,
        LSeries (IdealLogDerivative.coeff (RayQuotient.idealCharacter M H hH χ)) s) /
          (RayQuotient.classNumber M H : ℂ) := by
  have heq : (fun n => (quotientClassCoeff M H n : ℂ)) =
      (RayQuotient.classNumber M H : ℂ)⁻¹ • ∑ χ : RayQuotient.Characters M H,
        IdealLogDerivative.coeff (RayQuotient.idealCharacter M H hH χ) := by
    funext n
    rw [quotient_average_coeff M H hH]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq, LSeries_smul, LSeries_sum]
  · rw [div_eq_mul_inv, mul_comm]
  · intro χ _
    exact IdealLogDerivative.coeff_summable _ (RayQuotient.norm_idealCharacter_le_one M H hH χ) s hs

def quotientRemainder (F : rayCharacters M → ℂ → ℂ) (residue : ℂ) (s : ℂ) : ℂ :=
  (∑ χ : RayQuotient.Characters M H,
    -deriv (regularizedFamily M F residue (RayQuotient.toFullRay M H hH χ)) s /
      regularizedFamily M F residue (RayQuotient.toFullRay M H hH χ) s) /
        (RayQuotient.classNumber M H : ℂ)

theorem quotientRemainder_continuousOn {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) :
    ContinuousOn (quotientRemainder M H hH F residue) {s : ℂ | 1 ≤ s.re} := by
  intro s hs
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div_const
  apply tendsto_finsetSum
  intro χ _
  have h := regularizedFamily_analyticAt M hF (RayQuotient.toFullRay M H hH χ) s hs
  exact h.deriv.continuousAt.neg.div h.continuousAt
    (regularizedFamily_ne_zero M hF (RayQuotient.toFullRay M H hH χ) s hs)

theorem quotientRemainder_eqOn {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) :
    Set.EqOn (quotientRemainder M H hH F residue)
      (fun s => LSeries (fun n => (quotientClassCoeff M H n : ℂ)) s -
        (RayQuotient.classNumber M H : ℂ)⁻¹ / (s - 1)) {s : ℂ | 1 < s.re} := by
  intro s hs
  change quotientRemainder M H hH F residue s =
    LSeries (fun n => (quotientClassCoeff M H n : ℂ)) s -
      (RayQuotient.classNumber M H : ℂ)⁻¹ / (s - 1)
  rw [quotientRemainder, quotientClassCoeff_LSeries M H hH s hs]
  simp_rw [regularizedFamily_logDeriv M hF _ s hs, RayQuotient.toFullRay_eq_one]
  rw [Finset.sum_sub_distrib]
  have hsum : (∑ χ : RayQuotient.Characters M H, if χ = 1 then 1 / (s - 1) else (0 : ℂ)) =
      1 / (s - 1) := by simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hsum]
  have hlog (χ : RayQuotient.Characters M H) :
      -deriv (F (RayQuotient.toFullRay M H hH χ)) s / F (RayQuotient.toFullRay M H hH χ) s =
        LSeries (IdealLogDerivative.coeff (RayQuotient.idealCharacter M H hH χ)) s := by
    rw [RayQuotient.idealCharacter_eq_fullRay]
    exact (IdealLogDerivative.coeff_LSeries_eq_neg_logDeriv_of_eq _
      (norm_idealCharacter_le_one M _) (F _) (hF.eq_series _) s hs).symm
  simp_rw [hlog]
  ring

include hH in

theorem quotientClassCoeff_ratio_tendsto {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) :
    Tendsto (fun N : ℕ => cumsum (quotientClassCoeff M H) N / N)
      atTop (𝓝 ((RayQuotient.classNumber M H : ℝ)⁻¹)) := by
  apply WienerIkeharaTheorem'
    (IdealMangoldt.classCoeff_nonneg (RayQuotient.identityClass M H))
    (fun σ hσ => IdealMangoldt.classCoeff_summable_nterm (RayQuotient.identityClass M H) hσ)
    (IdealMangoldt.classCoeff_chebyshev (RayQuotient.identityClass M H))
    (quotientRemainder_continuousOn M H hH hF)
  simpa only [quotientClassCoeff, Complex.ofReal_inv, Complex.ofReal_natCast]
    using quotientRemainder_eqOn M H hH hF

end Quotient

end
end SevenEighths.PNT.RayAsymptotic

end OAI

end Source474

/- Original source: OAI/NumberTheory/DirichletL/PrimeCounting/Progressions.lean; sha256: 6fdc9180de7cbafd2e78164f97d2f9b6fdaa7d21523b6fe42a8f900ced80c665 -/
section Source475
namespace OAI

namespace SevenEighths.PNT

open Filter ArithmeticFunction LSeries
open scoped Topology

theorem residueClass_chebyshev {q : ℕ} (a : ZMod q) :
    ∃ C : ℝ, ∀ N : ℕ,
      cumsum (fun n : ℕ => ‖(vonMangoldt.residueClass a n : ℂ)‖) N ≤ C * N := by
  obtain ⟨C, hC⟩ := vonMangoldt_cheby
  refine ⟨C, fun N => le_trans ?_ (hC N)⟩
  unfold cumsum
  apply Finset.sum_le_sum
  intro n hn
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (vonMangoldt.residueClass_nonneg a n),
    abs_of_nonneg vonMangoldt_nonneg] using vonMangoldt.residueClass_le a n

theorem residueClass_summable {q : ℕ} (a : ZMod q) {σ : ℝ} (hσ : 1 < σ) :
    Summable (nterm (fun n => (vonMangoldt.residueClass a n : ℂ)) σ) := by
  have hs : LSeriesSummable (fun n => (vonMangoldt.residueClass a n : ℂ)) (σ : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
      lt_of_le_of_lt (vonMangoldt.abscissaOfAbsConv_residueClass_le_one a) (by
        exact_mod_cast hσ)
  simpa only [← nterm_eq_norm_term] using hs.norm

theorem residueClass_ratio_tendsto {q : ℕ} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    Tendsto (fun N : ℕ => cumsum (vonMangoldt.residueClass a) N / N)
      atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  apply WienerIkeharaTheorem'
    (vonMangoldt.residueClass_nonneg a)
    (fun σ hσ => residueClass_summable a hσ)
    (residueClass_chebyshev a)
    (vonMangoldt.continuousOn_LFunctionResidueClassAux a)
  simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using
    vonMangoldt.eqOn_LFunctionResidueClassAux ha

end SevenEighths.PNT

end OAI

end Source475

/- Original source: OAI/NumberTheory/DirichletL/PrimeCounting/PrimeMass.lean; sha256: 0117055741a1b13bfdab6f68b2ee8965eba05b4d59339aa6ec3a5574e0bcc408 -/
section Source476
namespace OAI

namespace SevenEighths.PNT

open Filter ArithmeticFunction
open scoped Topology BigOperators

theorem cumsum_div_tendsto_zero_of_summable_div {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hzero : f 0 = 0)
    (hsum : Summable (fun n => f n / n)) :
    Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 0) := by
  let F : ℕ → ℕ → ℝ := fun N n => if n < N then f n / N else 0
  have hlim (n : ℕ) : Tendsto (fun N => F N n) atTop (𝓝 0) := by
    apply (tendsto_const_div_atTop_nhds_zero_nat (f n)).congr'
    filter_upwards [eventually_gt_atTop n] with N hN
    simp [F, hN]
  have hbound : ∀ N n, ‖F N n‖ ≤ f n / n := by
    intro N n
    by_cases hn : n = 0
    · subst n
      simp [F, hzero]
    by_cases hN : n < N
    · simp only [F, ite_eq_left hN, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (hf n) (Nat.cast_nonneg N))]
      exact div_le_div_of_nonneg_left (hf n)
        (show (0 : ℝ) < n by exact_mod_cast Nat.pos_of_ne_zero hn)
        (show (n : ℝ) ≤ N by exact_mod_cast hN.le)
    · simp only [F, ite_eq_right hN, norm_zero]
      exact div_nonneg (hf n) (by positivity)
  have h := tendsto_tsum_of_dominated_convergence hsum hlim
    (Filter.Eventually.of_forall hbound)
  have heq (N : ℕ) : (∑' n, F N n) = cumsum f N / N := by
    rw [tsum_eq_sum (s := Finset.range N) (fun n hn => by
      simp only [Finset.mem_range] at hn
      simp [F, hn])]
    rw [cumsum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    simp [F, Finset.mem_range.mp hn]
  simpa only [heq, tsum_zero] using h

theorem retained_ratio_tendsto {f : ℕ → ℝ} {A : ℝ} (keep : ℕ → Prop)
    [DecidablePred keep] (hf : ∀ n, 0 ≤ f n) (hzero : f 0 = 0)
    (hmass : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A))
    (hremainder : Summable (fun n => (if keep n then 0 else f n) / n)) :
    Tendsto (fun N : ℕ => cumsum (fun n => if keep n then f n else 0) N / N)
      atTop (𝓝 A) := by
  have hrem := cumsum_div_tendsto_zero_of_summable_div
    (f := fun n => if keep n then 0 else f n)
    (fun n => by split_ifs <;> first | exact le_rfl | exact hf n)
    (by simp [hzero]) hremainder
  have h := hmass.sub hrem
  have heq (N : ℕ) :
      cumsum f N / N - cumsum (fun n => if keep n then 0 else f n) N / N =
      cumsum (fun n => if keep n then f n else 0) N / N := by
    rw [← sub_div]
    congr 1
    simp only [cumsum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    split_ifs <;> simp
  simpa only [heq, sub_zero] using h

theorem prime_residueClass_ratio_tendsto {q : ℕ} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    Tendsto (fun N : ℕ =>
      cumsum (fun n => if n.Prime then vonMangoldt.residueClass a n else 0) N / N)
      atTop (𝓝 ((q.totient : ℝ)⁻¹)) :=
  retained_ratio_tendsto Nat.Prime (vonMangoldt.residueClass_nonneg a)
    (vonMangoldt.residueClass_apply_zero a) (residueClass_ratio_tendsto a ha)
    (vonMangoldt.summable_residueClass_non_primes_div a)

end SevenEighths.PNT

end OAI

end Source476

/- Original source: OAI/NumberTheory/DirichletL/PrimeCounting/IdealPrimeMass.lean; sha256: b5eed6cc5c03c507d2fe0f098f390778e33e5c3c5d28b5412978bc5cd49da909 -/
section Source477
namespace OAI

namespace SevenEighths.PNT.IdealPrimeMass

open ActualEisensteinCubic ArithmeticFunction Filter
open SevenEighths.IdealMangoldt
open scoped BigOperators Classical Topology

noncomputable section

def primeClassCoeff (C : Set (Ideal O)) (n : ℕ) : ℝ :=
  classCoeff {I | I ∈ C ∧ Prime I} n

def higherClassCoeff (C : Set (Ideal O)) (n : ℕ) : ℝ :=
  classCoeff {I | I ∈ C ∧ ¬Prime I} n

theorem value_prime {P : Ideal O} (hP : Prime P) : value P = Real.log (Ideal.absNorm P) := by
  simpa only [pow_one] using value_pow hP (k := 1) (by decide)

theorem prime_of_isPrimePow_of_norm_prime {I : Ideal O}
    (hI : IsPrimePow I) (hn : (Ideal.absNorm I).Prime) : Prime I := by
  obtain ⟨P, k, hP, hk, rfl⟩ := hI
  rw [map_pow] at hn
  rw [hn.eq_one_of_pow, pow_one]
  exact hP

theorem value_eq_zero_of_nonprime_of_norm_prime {I : Ideal O}
    (hI : ¬Prime I) (hn : (Ideal.absNorm I).Prime) : value I = 0 := by
  apply ite_eq_right
  exact fun hpow => hI (prime_of_isPrimePow_of_norm_prime hpow hn)

theorem primeClassCoeff_eq_sum_log (C : Set (Ideal O)) (n : ℕ) :
    primeClassCoeff C n =
      ∑ P ∈ (normFiber n).filter (fun P => P ∈ C ∧ Prime P), Real.log (Ideal.absNorm P) := by
  unfold primeClassCoeff classCoeff coeff
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases h : I ∈ C ∧ Prime I
  · simp [h, value_prime h.2]
  · simp only [Set.mem_ofPred_eq, h, ite_false, zero_mul]

theorem primeClassCoeff_nonneg (C : Set (Ideal O)) (n : ℕ) : 0 ≤ primeClassCoeff C n :=
  classCoeff_nonneg _ n

theorem higherClassCoeff_nonneg (C : Set (Ideal O)) (n : ℕ) : 0 ≤ higherClassCoeff C n :=
  classCoeff_nonneg _ n

theorem classCoeff_eq_prime_add_higher (C : Set (Ideal O)) (n : ℕ) :
    classCoeff C n = primeClassCoeff C n + higherClassCoeff C n := by
  unfold primeClassCoeff higherClassCoeff classCoeff coeff
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hC : I ∈ C <;> by_cases hP : Prime I <;> simp [hC, hP]

@[simp] theorem higherClassCoeff_zero (C : Set (Ideal O)) : higherClassCoeff C 0 = 0 :=
  coeff_eq_zero_of_not_primePow not_isPrimePow_zero _

@[simp] theorem primeClassCoeff_zero (C : Set (Ideal O)) : primeClassCoeff C 0 = 0 :=
  coeff_eq_zero_of_not_primePow not_isPrimePow_zero _

theorem higherClassCoeff_eq_zero_of_prime (C : Set (Ideal O)) {n : ℕ} (hn : n.Prime) :
    higherClassCoeff C n = 0 := by
  apply Finset.sum_eq_zero
  intro I hI
  simp only [Set.mem_ofPred_eq]
  split_ifs with h
  · rw [value_eq_zero_of_nonprime_of_norm_prime h.2
      (by simpa only [(mem_normFiber n I).mp hI] using hn), mul_zero]
  · exact zero_mul _

theorem higherClassCoeff_le_nonprime_vonMangoldt (C : Set (Ideal O)) (n : ℕ) :
    higherClassCoeff C n ≤ 2 * (if n.Prime then 0 else vonMangoldt n) := by
  by_cases hn : n.Prime
  · rw [higherClassCoeff_eq_zero_of_prime C hn, ite_eq_left hn, mul_zero]
  · rw [ite_eq_right hn]
    exact classCoeff_le_two_vonMangoldt _ n

theorem summable_nonprime_vonMangoldt_div :
    Summable (fun n : ℕ => (if n.Prime then 0 else vonMangoldt n) / n) := by
  have h := vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)
  simpa only [vonMangoldt.residueClass, Subsingleton.elim (α := ZMod 1) _ 0,
    Set.ofPred_true, Set.indicator_univ] using h

theorem higherClassCoeff_summable_div (C : Set (Ideal O)) :
    Summable (fun n : ℕ => higherClassCoeff C n / n) := by
  apply (summable_nonprime_vonMangoldt_div.mul_left 2).of_nonneg_of_le
  · intro n
    exact div_nonneg (higherClassCoeff_nonneg C n) (Nat.cast_nonneg n)
  · intro n
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (higherClassCoeff_le_nonprime_vonMangoldt C n)
      (Nat.cast_nonneg n)

theorem higherClassCoeff_ratio_tendsto_zero (C : Set (Ideal O)) :
    Tendsto (fun N : ℕ => cumsum (higherClassCoeff C) N / N) atTop (𝓝 0) :=
  cumsum_div_tendsto_zero_of_summable_div (higherClassCoeff_nonneg C)
    (higherClassCoeff_zero C) (higherClassCoeff_summable_div C)

theorem primeClassCoeff_ratio_tendsto (C : Set (Ideal O)) {A : ℝ}
    (h : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A)) :
    Tendsto (fun N : ℕ => cumsum (primeClassCoeff C) N / N) atTop (𝓝 A) := by
  have h' := h.sub (higherClassCoeff_ratio_tendsto_zero C)
  have heq (N : ℕ) :
      cumsum (classCoeff C) N / N - cumsum (higherClassCoeff C) N / N =
        cumsum (primeClassCoeff C) N / N := by
    rw [← sub_div]
    congr 1
    simp only [cumsum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [classCoeff_eq_prime_add_higher, add_sub_cancel_right]
  simpa only [heq, sub_zero] using h'

def primeIdealsBelow (C : Set (Ideal O)) (N : ℕ) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_le (S := O) N).toFinset.filter
    (fun P => P ∈ C ∧ Prime P ∧ Ideal.absNorm P < N)

@[simp] theorem mem_primeIdealsBelow (C : Set (Ideal O)) (N : ℕ) (P : Ideal O) :
    P ∈ primeIdealsBelow C N ↔ P ∈ C ∧ Prime P ∧ Ideal.absNorm P < N := by
  simp only [primeIdealsBelow, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  exact ⟨fun h => h.2, fun h => ⟨h.2.2.le, h⟩⟩

theorem zero_not_mem_primeIdealsBelow (C : Set (Ideal O)) (N : ℕ) :
    (0 : Ideal O) ∉ primeIdealsBelow C N := by
  intro h
  exact ((mem_primeIdealsBelow C N 0).mp h).2.1.ne_zero rfl

def primeLogMass (C : Set (Ideal O)) (N : ℕ) : ℝ :=
  ∑ P ∈ primeIdealsBelow C N, Real.log (Ideal.absNorm P)

theorem primeLogMass_eq_cumsum (C : Set (Ideal O)) (N : ℕ) :
    primeLogMass C N = cumsum (primeClassCoeff C) N := by
  have hmap : ∀ P ∈ primeIdealsBelow C N, Ideal.absNorm P ∈ Finset.range N := by
    intro P hP
    exact Finset.mem_range.mpr ((mem_primeIdealsBelow C N P).mp hP).2.2
  rw [primeLogMass, ← Finset.sum_fiberwise_of_maps_to hmap]
  unfold cumsum
  apply Finset.sum_congr rfl
  intro n hn
  rw [primeClassCoeff_eq_sum_log]
  apply Finset.sum_congr
  · ext P
    simp only [Finset.mem_filter, mem_primeIdealsBelow, mem_normFiber]
    constructor
    · rintro ⟨⟨hC, hP, hN⟩, heq⟩
      exact ⟨heq, hC, hP⟩
    · rintro ⟨heq, hC, hP⟩
      exact ⟨⟨hC, hP, heq ▸ Finset.mem_range.mp hn⟩, heq⟩
  · intro P hP
    rfl

theorem primeLogMass_ratio_tendsto (C : Set (Ideal O)) {A : ℝ}
    (h : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A)) :
    Tendsto (fun N : ℕ => primeLogMass C N / N) atTop (𝓝 A) := by
  simpa only [primeLogMass_eq_cumsum] using primeClassCoeff_ratio_tendsto C h

end

end SevenEighths.PNT.IdealPrimeMass

end OAI

end Source477

/- Original source: OAI/NumberTheory/DirichletL/Hecke/RayPrimes.lean; sha256: 9b402e301e534f86854a4c403fd4f9a51c1ae55bb074222a78364987900e93d6 -/
section Source478
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.HeckeRayPrimes
open HeckeFamily
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

theorem analytic_family : PNT.RayAsymptotic.AnalyticFamily M
    (fun χ => LFunction (HeckeRayFamily.character M χ))
    (HeckeOrigin.poleRemoved (HeckeRayFamily.character M 1) 1) := by
  refine ⟨?_, ?_, ?_, ?_, HeckeRayFamily.principal_pole_ne_zero M⟩
  · intro χ s hs
    exact LFunction_eq_series _ hs
  · intro χ s hs hpole
    rcases hpole with hχ | hs1
    · exact (HeckeRayFamily.character_entire M χ hχ).analyticAt s
    · apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
      have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
      filter_upwards [isOpen_ne.mem_nhds hs0, isOpen_ne.mem_nhds hs1] with z hz0 hz1
      exact LFunction_differentiableAt _ hz0 (Or.inl hz1)
  · intro χ s hs hpole
    exact HeckeRayFamily.character_boundary_ne_zero M χ hs hpole.symm
  · apply PNT.RayAsymptotic.principalRegularization_analyticAt_of_local
      _ (HeckeOrigin.poleRemoved (HeckeRayFamily.character M 1))
      ((HeckeOrigin.poleRemoved_entire _).analyticAt 1)
    filter_upwards [isOpen_ne.mem_nhds (by norm_num : (1 : ℂ) ≠ 0)] with s hs0
    intro hs1
    exact (HeckeOrigin.poleRemoved_eq _ hs0 hs1).symm

theorem classCoeff_ratio_tendsto :
    Tendsto (fun N : ℕ => cumsum (PNT.RayAsymptotic.classCoeff M) N / N)
      atTop (𝓝 ((RayOrthogonality.rayCard M : ℝ)⁻¹)) :=
  PNT.RayAsymptotic.classCoeff_ratio_tendsto M (analytic_family M)

theorem quotientClassCoeff_ratio_tendsto
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H) :
    Tendsto (fun N : ℕ => cumsum (PNT.RayAsymptotic.quotientClassCoeff M H) N / N)
      atTop (𝓝 ((RayQuotient.classNumber M H : ℝ)⁻¹)) :=
  PNT.RayAsymptotic.quotientClassCoeff_ratio_tendsto M H hH (analytic_family M)

theorem primeLogMass_ratio_tendsto :
    Tendsto (fun N : ℕ => PNT.IdealPrimeMass.primeLogMass (RayOrthogonality.principalIdeals M) N / N)
      atTop (𝓝 ((RayOrthogonality.rayCard M : ℝ)⁻¹)) :=
  PNT.IdealPrimeMass.primeLogMass_ratio_tendsto _ (classCoeff_ratio_tendsto M)

theorem quotientPrimeLogMass_ratio_tendsto
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H) :
    Tendsto (fun N : ℕ => PNT.IdealPrimeMass.primeLogMass (RayQuotient.identityClass M H) N / N)
      atTop (𝓝 ((RayQuotient.classNumber M H : ℝ)⁻¹)) :=
  PNT.IdealPrimeMass.primeLogMass_ratio_tendsto _ (quotientClassCoeff_ratio_tendsto M H hH)

end SevenEighths.HeckeRayPrimes

end

end OAI

end Source478

/- Original source: OAI/NumberTheory/DirichletL/PrimeCounting/AnnularPrimeMass.lean; sha256: d69022ebfc0c84ea6729ff47241c1fb7105c3d027070ab817f194e3da12b8949 -/
section Source479
namespace OAI

namespace SevenEighths.PNT.AnnularPrimeMass

open ActualEisensteinCubic ArithmeticFunction Filter MeasureTheory
open SevenEighths.IdealMangoldt SevenEighths.PNT.IdealPrimeMass
open scoped BigOperators Classical Topology ContDiff

noncomputable section

def cumulative (f : ℕ → ℝ) (t : ℝ) : ℝ := cumsum f (⌊t⌋₊ + 1)

def scaledCumulative (f : ℕ → ℝ) (x y : ℝ) : ℝ := cumulative f (x * y) / x

theorem cumulative_ratio_tendsto {f : ℕ → ℝ} {A : ℝ}
    (h : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A)) :
    Tendsto (fun t : ℝ => cumulative f t / t) atTop (𝓝 A) := by
  have ht : Tendsto (fun t : ℝ => ⌊t⌋₊ + 1) atTop atTop :=
    tendsto_atTop_mono (fun _ => Nat.le_succ _) tendsto_nat_floor_atTop
  have hr : Tendsto (fun t : ℝ => ((⌊t⌋₊ + 1 : ℕ) : ℝ) / t) atTop (𝓝 1) := by
    convert (tendsto_nat_floor_div_atTop (R := ℝ)).add
      (show Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) by simpa only [one_div] using tendsto_inv_atTop_zero) using 1 <;> simp [add_div]
  convert (h.comp ht).mul hr using 1
  · ext t
    simp only [Function.comp_def, cumulative]
    field_simp
  · simp

theorem scaledCumulative_tendsto {f : ℕ → ℝ} {A : ℝ}
    (h : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A))
    {y : ℝ} (hy : 0 < y) :
    Tendsto (fun x : ℝ => scaledCumulative f x y) atTop (𝓝 (A * y)) := by
  have ht : Tendsto (fun x : ℝ => x * y) atTop atTop := tendsto_id.atTop_mul_const hy
  apply ((cumulative_ratio_tendsto h).comp ht).mul_const y |>.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold scaledCumulative
  dsimp only [Function.comp_def]
  field_simp

theorem cumulative_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (t : ℝ) :
    0 ≤ cumulative f t := cumsum_nonneg hf _

theorem scaledCumulative_bound {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ N : ℕ, cumsum f N ≤ C * N)
    {x y b : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y) (hyb : y ≤ b) :
    ‖scaledCumulative f x y‖ ≤ C * (b + 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [scaledCumulative, Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg (cumulative_nonneg hf _) hx0.le)]
  calc
    cumulative f (x * y) / x ≤ (C * (⌊x * y⌋₊ + 1 : ℕ)) / x := by
      exact div_le_div_of_nonneg_right (hbound _) hx0.le
    _ ≤ (C * (x * y + 1)) / x := by
      gcongr
      push_cast
      linarith [Nat.floor_le (mul_nonneg hx0.le hy)]
    _ ≤ C * (b + 1) := by
      rw [div_le_iff₀ hx0]
      nlinarith [mul_le_mul_of_nonneg_left hyb hx0.le,
        mul_nonneg hC (sub_nonneg.mpr hx)]

theorem measurable_cumulative (f : ℕ → ℝ) : Measurable (cumulative f) :=
  (measurable_of_countable (cumsum f)).comp (measurable_id.nat_floor.add_const 1)

theorem measurable_scaledCumulative (f : ℕ → ℝ) (x : ℝ) :
    Measurable (scaledCumulative f x) :=
  ((measurable_cumulative f).comp (measurable_const.mul measurable_id)).div_const x

def annularSum (f : ℕ → ℝ) (φ : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊x * a⌋₊ ⌊x * b⌋₊, f n * φ (n / x)

theorem annularSum_div_eq_integral (f : ℕ → ℝ) (φ : ℝ → ℝ)
    (hφ : Differentiable ℝ φ) (hφ' : Continuous (deriv φ))
    {a b x : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hx : 0 < x)
    (hφa : φ a = 0) (hφb : φ b = 0) :
    annularSum f φ a b x / x =
      -(∫ y in a..b, deriv φ y * scaledCumulative f x y) := by
  let g : ℝ → ℝ := fun t => φ (t / x)
  have hg (t : ℝ) : HasDerivAt g (deriv φ (t / x) / x) t := by
    convert (hφ (t / x)).hasDerivAt.comp t ((hasDerivAt_id t).div_const x) using 1 <;>
      simp only [g, Function.comp_def, div_eq_mul_inv, id_eq, one_mul]
  have hgc : Continuous (deriv g) := by
    have heq : deriv g = fun t => deriv φ (t / x) / x := funext (fun t => (hg t).deriv)
    rw [heq]
    exact (hφ'.comp (continuous_id.div_const x)).div_const x
  have h := sum_mul_eq_sub_sub_integral_mul f (a := x * a) (b := x * b)
    (mul_nonneg hx.le ha) (mul_le_mul_of_nonneg_left hab hx.le)
    (fun t _ => (hg t).differentiableAt) hgc.integrableOn_Icc
  have hcum (t : ℝ) : (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, f k) = cumulative f t := by
    simp only [cumulative, cumsum, Nat.range_succ_eq_Icc_zero]
  simp_rw [hcum, (hg _).deriv] at h
  have hga : g (x * a) = 0 := by simp only [g, mul_div_cancel_left₀ _ hx.ne', hφa]
  have hgb : g (x * b) = 0 := by simp only [g, mul_div_cancel_left₀ _ hx.ne', hφb]
  rw [hga, hgb, zero_mul, zero_mul, sub_zero, zero_sub,
    ← intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left hab hx.le)] at h
  have hs : annularSum f φ a b x =
      -(∫ t in x * a..x * b, (deriv φ (t / x) / x) * cumulative f t) := by
    rw [← h]
    unfold annularSum g
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hs, neg_div]
  congr 1
  have hi := intervalIntegral.integral_comp_mul_left
    (fun t => (deriv φ (t / x) / x) * cumulative f t) hx.ne' (a := a) (b := b)
  simp only [smul_eq_mul, ← div_eq_inv_mul] at hi
  rw [← hi]
  apply intervalIntegral.integral_congr
  intro y hy
  simp only [mul_div_cancel_left₀ _ hx.ne', scaledCumulative]
  ring

theorem integral_scaledCumulative_tendsto {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {A C a b : ℝ} (hC : 0 ≤ C) (hbound : ∀ N : ℕ, cumsum f N ≤ C * N)
    (hmass : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A))
    (ha : 0 < a) (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g) :
    Tendsto (fun x : ℝ => ∫ y in a..b, g y * scaledCumulative f x y) atTop
      (𝓝 (∫ y in a..b, g y * (A * y))) := by
  simp_rw [intervalIntegral.integral_of_le hab]
  apply tendsto_integral_filter_of_dominated_convergence (fun y => ‖g y‖ * (C * (b + 1)))
  · exact Eventually.of_forall (fun x =>
      (hg.measurable.mul (measurable_scaledCumulative f x)).aestronglyMeasurable)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (scaledCumulative_bound hf hC hbound hx (ha.le.trans hy.1.le) hy.2) (norm_nonneg _)
  · exact (hg.norm.mul_const _).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact (scaledCumulative_tendsto hmass (ha.trans hy.1)).const_mul (g y)

theorem annularSum_div_tendsto {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {A C a b : ℝ} (hC : 0 ≤ C) (hbound : ∀ N : ℕ, cumsum f N ≤ C * N)
    (hmass : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A))
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (hφ' : Continuous (deriv φ))
    (ha : 0 < a) (hab : a ≤ b) (hφa : φ a = 0) (hφb : φ b = 0) :
    Tendsto (fun x : ℝ => annularSum f φ a b x / x) atTop
      (𝓝 (A * ∫ y in a..b, φ y)) := by
  have h := (integral_scaledCumulative_tendsto hf hC hbound hmass ha hab (deriv φ) hφ').neg
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun y : ℝ => y) (u' := fun _ => (1 : ℝ)) (v := φ) (v' := deriv φ)
    (fun y _ => hasDerivAt_id y) (fun y _ => (hφ y).hasDerivAt)
    (continuous_const.intervalIntegrable a b) (hφ'.intervalIntegrable a b)
  have heq : -(∫ y in a..b, deriv φ y * (A * y)) = A * ∫ y in a..b, φ y := by
    have hfun : (fun y => deriv φ y * (A * y)) = fun y => A * (y * deriv φ y) := by
      ext y
      ring
    rw [hfun, intervalIntegral.integral_const_mul, hibp, hφa, hφb]
    simp
  rw [heq] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (annularSum_div_eq_integral f φ hφ hφ' ha.le hab hx hφa hφb).symm

def annularPrimeIdeals (C : Set (Ideal O)) (a b x : ℝ) : Finset (Ideal O) :=
  (primeIdealsBelow C (⌊x * b⌋₊ + 1)).filter (fun P => ⌊x * a⌋₊ < Ideal.absNorm P)

@[simp] theorem mem_annularPrimeIdeals (C : Set (Ideal O)) (a b x : ℝ) (P : Ideal O) :
    P ∈ annularPrimeIdeals C a b x ↔
      P ∈ C ∧ Prime P ∧ ⌊x * a⌋₊ < Ideal.absNorm P ∧ Ideal.absNorm P ≤ ⌊x * b⌋₊ := by
  simp only [annularPrimeIdeals, Finset.mem_filter, mem_primeIdealsBelow, Nat.lt_succ_iff]
  tauto

def primeAnnularSum (C : Set (Ideal O)) (φ : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∑ P ∈ annularPrimeIdeals C a b x, φ (Ideal.absNorm P / x)

def primeLogAnnularSum (C : Set (Ideal O)) (φ : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∑ P ∈ annularPrimeIdeals C a b x, Real.log (Ideal.absNorm P) * φ (Ideal.absNorm P / x)

theorem primeLogAnnularSum_eq (C : Set (Ideal O)) (φ : ℝ → ℝ) (a b x : ℝ) :
    primeLogAnnularSum C φ a b x = annularSum (primeClassCoeff C) φ a b x := by
  have hmap : ∀ P ∈ annularPrimeIdeals C a b x,
      Ideal.absNorm P ∈ Finset.Ioc ⌊x * a⌋₊ ⌊x * b⌋₊ := by
    intro P hP
    exact Finset.mem_Ioc.mpr ((mem_annularPrimeIdeals C a b x P).mp hP).2.2
  rw [primeLogAnnularSum, ← Finset.sum_fiberwise_of_maps_to hmap]
  unfold annularSum
  apply Finset.sum_congr rfl
  intro n hn
  rw [primeClassCoeff_eq_sum_log, Finset.sum_mul]
  apply Finset.sum_congr
  · ext P
    simp only [Finset.mem_filter, mem_annularPrimeIdeals, mem_normFiber]
    constructor
    · rintro ⟨⟨hC, hP, hN⟩, heq⟩
      exact ⟨heq, hC, hP⟩
    · rintro ⟨heq, hC, hP⟩
      exact ⟨⟨hC, hP, heq ▸ Finset.mem_Ioc.mp hn⟩, heq⟩
  · intro P hP
    rw [(mem_normFiber n P).mp (Finset.mem_filter.mp hP).1]

theorem primeClassCoeff_chebyshev (C : Set (Ideal O)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, cumsum (primeClassCoeff C) N ≤ B * N := by
  obtain ⟨B, hB⟩ := classCoeff_chebyshev {I | I ∈ C ∧ Prime I}
  have hbound (N : ℕ) : cumsum (primeClassCoeff C) N ≤ B * N := by
    convert hB N using 1
    congr 1
    funext n
    exact (Complex.norm_of_nonneg (primeClassCoeff_nonneg C n)).symm
  refine ⟨B, ?_, hbound⟩
  have h := (cumsum_nonneg (primeClassCoeff_nonneg C) 1).trans (hbound 1)
  simpa only [Nat.cast_one, mul_one, Pi.zero_apply] using h

theorem primeLogAnnularSum_div_tendsto (C : Set (Ideal O)) {A a b : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (hφ' : Continuous (deriv φ))
    (ha : 0 < a) (hab : a ≤ b) (hφa : φ a = 0) (hφb : φ b = 0) :
    Tendsto (fun x : ℝ => primeLogAnnularSum C φ a b x / x) atTop
      (𝓝 (A * ∫ y in a..b, φ y)) := by
  obtain ⟨B, hB, hbound⟩ := primeClassCoeff_chebyshev C
  simpa only [primeLogAnnularSum_eq] using annularSum_div_tendsto
    (primeClassCoeff_nonneg C) hB hbound (primeClassCoeff_ratio_tendsto C hmass)
    φ hφ hφ' ha hab hφa hφb

theorem norm_bounds_of_mem_annularPrimeIdeals {C : Set (Ideal O)} {a b x : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hx : 0 < x) {P : Ideal O}
    (hP : P ∈ annularPrimeIdeals C a b x) :
    x * a < (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ x * b := by
  have h := (mem_annularPrimeIdeals C a b x P).mp hP
  exact ⟨(Nat.floor_lt (mul_nonneg hx.le ha)).mp h.2.2.1,
    (Nat.le_floor_iff (mul_nonneg hx.le (ha.trans hab))).mp h.2.2.2⟩

theorem ratio_mem_of_mem_annularPrimeIdeals {C : Set (Ideal O)} {a b x : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hx : 0 < x) {P : Ideal O}
    (hP : P ∈ annularPrimeIdeals C a b x) :
    (Ideal.absNorm P : ℝ) / x ∈ Set.Icc a b := by
  obtain ⟨hl, hu⟩ := norm_bounds_of_mem_annularPrimeIdeals ha hab hx hP
  exact ⟨(le_div_iff₀ hx).mpr (by nlinarith), (div_le_iff₀ hx).mpr (by nlinarith)⟩

theorem log_norm_difference_bound {a b x : ℝ} (ha : 0 < a) (_hab : a ≤ b)
    (hx : 0 < x) {n : ℕ} (hn : (n : ℝ) / x ∈ Set.Icc a b) :
    |Real.log x - Real.log n| ≤ |Real.log a| + |Real.log b| := by
  have hn0 : 0 < (n : ℝ) := by
    have h := (le_div_iff₀ hx).mp hn.1
    exact (mul_pos ha hx).trans_le h
  have hl := Real.log_le_log ha hn.1
  have hu := Real.log_le_log (ha.trans_le hn.1) hn.2
  rw [Real.log_div hn0.ne' hx.ne'] at hl hu
  apply abs_le.mpr
  constructor <;> linarith [le_abs_self (Real.log a), neg_abs_le (Real.log a),
    le_abs_self (Real.log b), neg_abs_le (Real.log b), abs_nonneg (Real.log a),
    abs_nonneg (Real.log b)]

theorem annularPrime_card_div_bound (C : Set (Ideal O)) {B a b x : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ N : ℕ, cumsum (primeClassCoeff C) N ≤ B * N)
    (ha : 0 < a) (hab : a ≤ b) (hx : 1 ≤ x) (hxa : 1 < x * a) :
    ((annularPrimeIdeals C a b x).card : ℝ) / x ≤ B * (b + 1) / Real.log (x * a) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog : 0 < Real.log (x * a) := Real.log_pos hxa
  have hlower : Real.log (x * a) * (annularPrimeIdeals C a b x).card ≤
      ∑ P ∈ annularPrimeIdeals C a b x, Real.log (Ideal.absNorm P) := by
    rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro P hP
    exact Real.log_le_log (mul_pos hx0 ha)
      (norm_bounds_of_mem_annularPrimeIdeals ha.le hab hx0 hP).1.le
  have hupper : (∑ P ∈ annularPrimeIdeals C a b x, Real.log (Ideal.absNorm P)) ≤
      cumsum (primeClassCoeff C) (⌊x * b⌋₊ + 1) := by
    rw [← primeLogMass_eq_cumsum, primeLogMass]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro P hP _
    rw [← value_prime ((mem_primeIdealsBelow C _ P).mp hP).2.1]
    exact value_nonneg P
  have hnorm := scaledCumulative_bound (primeClassCoeff_nonneg C) hB hbound hx
    (ha.le.trans hab) (le_refl b)
  have hcum : cumsum (primeClassCoeff C) (⌊x * b⌋₊ + 1) / x ≤ B * (b + 1) :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, scaledCumulative, cumulative] using hnorm)
  apply (le_div_iff₀ hlog).mpr
  calc
    ((annularPrimeIdeals C a b x).card : ℝ) / x * Real.log (x * a) =
        (Real.log (x * a) * (annularPrimeIdeals C a b x).card) / x := by ring
    _ ≤ (∑ P ∈ annularPrimeIdeals C a b x, Real.log (Ideal.absNorm P)) / x :=
      div_le_div_of_nonneg_right hlower hx0.le
    _ ≤ cumsum (primeClassCoeff C) (⌊x * b⌋₊ + 1) / x :=
      div_le_div_of_nonneg_right hupper hx0.le
    _ ≤ _ := hcum

theorem primeAnnularSum_log_error_bound (C : Set (Ideal O)) (φ : ℝ → ℝ)
    {B M a b x : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ N : ℕ, cumsum (primeClassCoeff C) N ≤ B * N)
    (hM : 0 ≤ M) (hφ : ∀ y ∈ Set.Icc a b, |φ y| ≤ M)
    (ha : 0 < a) (hab : a ≤ b) (hx : 1 ≤ x) (hxa : 1 < x * a) :
    ‖Real.log x * primeAnnularSum C φ a b x / x - primeLogAnnularSum C φ a b x / x‖ ≤
      ((|Real.log a| + |Real.log b|) * M) * (B * (b + 1) / Real.log (x * a)) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have heq : Real.log x * primeAnnularSum C φ a b x - primeLogAnnularSum C φ a b x =
      ∑ P ∈ annularPrimeIdeals C a b x,
        (Real.log x - Real.log (Ideal.absNorm P)) * φ (Ideal.absNorm P / x) := by
    simp only [primeAnnularSum, primeLogAnnularSum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      sub_mul]
  rw [← sub_div, heq, norm_div, Real.norm_of_nonneg hx0.le]
  calc
    _ ≤ (∑ P ∈ annularPrimeIdeals C a b x,
        ‖(Real.log x - Real.log (Ideal.absNorm P)) * φ (Ideal.absNorm P / x)‖) / x :=
      div_le_div_of_nonneg_right (norm_sum_le _ _) hx0.le
    _ ≤ (∑ _P ∈ annularPrimeIdeals C a b x, (|Real.log a| + |Real.log b|) * M) / x := by
      apply div_le_div_of_nonneg_right _ hx0.le
      apply Finset.sum_le_sum
      intro P hP
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hratio := ratio_mem_of_mem_annularPrimeIdeals ha.le hab hx0 hP
      exact mul_le_mul (log_norm_difference_bound ha hab hx0 hratio) (hφ _ hratio)
        (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = ((|Real.log a| + |Real.log b|) * M) * ((annularPrimeIdeals C a b x).card / x) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (annularPrime_card_div_bound C hB hbound ha hab hx hxa)
      (mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hM)

theorem primeAnnularSum_log_error_tendsto (C : Set (Ideal O)) (φ : ℝ → ℝ)
    (hφ : Continuous φ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun x : ℝ => Real.log x * primeAnnularSum C φ a b x / x -
      primeLogAnnularSum C φ a b x / x) atTop (𝓝 0) := by
  obtain ⟨B, hB, hbound⟩ := primeClassCoeff_chebyshev C
  obtain ⟨M, hMbound⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ.continuousOn
  have hM : 0 ≤ M := (norm_nonneg _).trans (hMbound a ⟨le_rfl, hab⟩)
  have hup : Tendsto (fun x : ℝ => ((|Real.log a| + |Real.log b|) * M) *
      (B * (b + 1) / Real.log (x * a))) atTop (𝓝 0) := by
    have hi := tendsto_inv_atTop_zero.comp
      (Real.tendsto_log_atTop.comp (tendsto_id.atTop_mul_const ha))
    convert (hi.const_mul (B * (b + 1))).const_mul ((|Real.log a| + |Real.log b|) * M)
      using 1 <;> simp only [div_eq_mul_inv, mul_zero, Function.comp_def, id_eq]
  apply squeeze_zero_norm' _ hup
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_id.atTop_mul_const ha).eventually_gt_atTop 1] with x hx hxa
  exact primeAnnularSum_log_error_bound C φ hB hbound hM
    (fun y hy => by simpa only [Real.norm_eq_abs] using hMbound y hy) ha hab hx hxa

theorem primeAnnularSum_log_div_tendsto (C : Set (Ideal O)) {A a b : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (hφ' : Continuous (deriv φ))
    (ha : 0 < a) (hab : a ≤ b) (hφa : φ a = 0) (hφb : φ b = 0) :
    Tendsto (fun x : ℝ => Real.log x * primeAnnularSum C φ a b x / x) atTop
      (𝓝 (A * ∫ y in a..b, φ y)) := by
  have h := (primeAnnularSum_log_error_tendsto C φ hφ.continuous ha hab).add
    (primeLogAnnularSum_div_tendsto C hmass φ hφ hφ' ha hab hφa hφb)
  simpa only [sub_add_cancel, zero_add] using h

theorem contDiff_powerWeight (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W)
    {a b : ℝ} (ha : 0 < a) (hsupp : Function.support W ⊆ Set.Ioo a b) (r : ℝ) :
    ContDiff ℝ ∞ (fun y => W y * y ^ r) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y = 0
  · subst y
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ha] with y hy
    have hWy : W y = 0 := Function.notMem_support.mp (by
      intro h
      exact (not_lt_of_ge (hsupp h).1.le) hy)
    simp only [hWy, zero_mul]
  · exact hW.contDiffAt.mul (Real.contDiffAt_rpow_const_of_ne hy)

def weightedPrimeAnnularSum (C : Set (Ideal O)) (W : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∑ P ∈ annularPrimeIdeals C a b x,
    W (Ideal.absNorm P / x) * (Ideal.absNorm P : ℝ) ^ (-5 / 6 : ℝ)

theorem weightedPrimeAnnularSum_normalization (C : Set (Ideal O)) (W : ℝ → ℝ)
    (a b : ℝ) {x : ℝ} (hx : 0 < x) :
    Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeAnnularSum C W a b x =
      Real.log x * primeAnnularSum C (fun y => W y * y ^ (-5 / 6 : ℝ)) a b x / x := by
  have heq : primeAnnularSum C (fun y => W y * y ^ (-5 / 6 : ℝ)) a b x =
      weightedPrimeAnnularSum C W a b x / x ^ (-5 / 6 : ℝ) := by
    unfold primeAnnularSum weightedPrimeAnnularSum
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro P hP
    dsimp only
    rw [Real.div_rpow (Nat.cast_nonneg _) hx.le]
    ring
  have hp : x ^ (-5 / 6 : ℝ) * x = x ^ (1 / 6 : ℝ) := by
    calc
      _ = x ^ (-5 / 6 : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ ((-5 / 6 : ℝ) + 1) := (Real.rpow_add hx _ _).symm
      _ = _ := by norm_num
  rw [heq, mul_div_assoc, div_div, hp]
  ring

theorem weightedPrimeAnnularSum_tendsto (C : Set (Ideal O)) {A a b : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W)
    (ha : 0 < a) (hab : a ≤ b) (hsupp : Function.support W ⊆ Set.Ioo a b) :
    Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeAnnularSum C W a b x)
      atTop (𝓝 (A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ))) := by
  let φ : ℝ → ℝ := fun y => W y * y ^ (-5 / 6 : ℝ)
  have hφ : ContDiff ℝ ∞ φ := contDiff_powerWeight W hW ha hsupp _
  have hWa : W a = 0 := Function.notMem_support.mp (fun h => (hsupp h).1.false)
  have hWb : W b = 0 := Function.notMem_support.mp (fun h => (hsupp h).2.false)
  have hφa : φ a = 0 := by simp only [φ, hWa, zero_mul]
  have hφb : φ b = 0 := by simp only [φ, hWb, zero_mul]
  have hint : (∫ y in a..b, φ y) = ∫ y, φ y := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hWy : W y = 0 := Function.notMem_support.mp
      (fun h => hy ⟨(hsupp h).1, (hsupp h).2.le⟩)
    simp only [φ, hWy, zero_mul]
  have h := primeAnnularSum_log_div_tendsto C hmass φ (hφ.differentiable (by simp))
    (hφ.continuous_deriv (by simp)) ha hab hφa hφb
  rw [hint] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (weightedPrimeAnnularSum_normalization C W a b hx).symm

theorem weightedPrimeAnnularSum_nat_tendsto (C : Set (Ideal O)) {A a b : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W)
    (ha : 0 < a) (hab : a ≤ b) (hsupp : Function.support W ⊆ Set.Ioo a b) :
    Tendsto (fun N : ℕ => Real.log N / (N : ℝ) ^ (1 / 6 : ℝ) *
      weightedPrimeAnnularSum C W a b N) atTop (𝓝 (A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ))) :=
  (weightedPrimeAnnularSum_tendsto C hmass W hW ha hab hsupp).comp tendsto_natCast_atTop_atTop

theorem exists_positive_support_annulus (W : ℝ → ℝ) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ Function.support W ⊆ Set.Ioo a b := by
  by_cases hne : (tsupport W).Nonempty
  · obtain ⟨m, hm, hmin⟩ := hc.exists_isMinOn hne continuous_id.continuousOn
    obtain ⟨M, hM, hmax⟩ := hc.exists_isMaxOn hne continuous_id.continuousOn
    have hm0 : 0 < m := hp hm
    have hmM : m ≤ M := hmin hM
    refine ⟨m / 2, M + 1, by positivity, by linarith, ?_⟩
    intro y hy
    have hyt : y ∈ tsupport W := subset_closure hy
    have hl : m ≤ y := hmin hyt
    have hu : y ≤ M := hmax hyt
    exact ⟨by linarith, by linarith⟩
  · refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
    intro y hy
    exact (hne ⟨y, subset_closure hy⟩).elim

theorem mem_annularPrimeIdeals_of_weight_ne_zero {C : Set (Ideal O)} {W : ℝ → ℝ}
    {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hx : 0 < x)
    {P : Ideal O} (hC : P ∈ C) (hP : Prime P) (hW : W (Ideal.absNorm P / x) ≠ 0) :
    P ∈ annularPrimeIdeals C a b x := by
  have hy := hsupp hW
  apply (mem_annularPrimeIdeals C a b x P).mpr
  refine ⟨hC, hP, ?_, ?_⟩
  · apply (Nat.floor_lt (mul_nonneg hx.le ha.le)).mpr
    have h := (lt_div_iff₀ hx).mp hy.1
    nlinarith
  · apply (Nat.le_floor_iff (mul_nonneg hx.le (ha.le.trans hab))).mpr
    have h := (div_lt_iff₀ hx).mp hy.2
    nlinarith

def primeWeightTerm (C : Set (Ideal O)) (W : ℝ → ℝ) (x : ℝ) (P : Ideal O) : ℝ :=
  if P ∈ C ∧ Prime P then W (Ideal.absNorm P / x) * (Ideal.absNorm P : ℝ) ^ (-5 / 6 : ℝ) else 0

def weightedPrimeSum (C : Set (Ideal O)) (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ᶠ P : Ideal O, primeWeightTerm C W x P

theorem primeWeightTerm_support_subset (C : Set (Ideal O)) (W : ℝ → ℝ)
    {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hx : 0 < x) :
    Function.support (primeWeightTerm C W x) ⊆ (annularPrimeIdeals C a b x : Set (Ideal O)) := by
  intro P hP
  change primeWeightTerm C W x P ≠ 0 at hP
  unfold primeWeightTerm at hP
  split_ifs at hP with h
  · exact mem_annularPrimeIdeals_of_weight_ne_zero ha hab hsupp hx h.1 h.2
      (left_ne_zero_of_mul hP)
  · exact (hP rfl).elim

theorem primeWeightTerm_hasFiniteSupport (C : Set (Ideal O)) (W : ℝ → ℝ)
    (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0) {x : ℝ} (hx : 0 < x) :
    (Function.support (primeWeightTerm C W x)).Finite := by
  obtain ⟨a, b, ha, hab, hsupp⟩ := exists_positive_support_annulus W hc hp
  exact (annularPrimeIdeals C a b x).finite_toSet.subset
    (primeWeightTerm_support_subset C W ha hab.le hsupp hx)

theorem weightedPrimeSum_eq_annular (C : Set (Ideal O)) (W : ℝ → ℝ)
    {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hx : 0 < x) :
    weightedPrimeSum C W x = weightedPrimeAnnularSum C W a b x := by
  rw [weightedPrimeSum, finsum_eq_finsetSum_of_support_subset _
    (primeWeightTerm_support_subset C W ha hab hsupp hx)]
  apply Finset.sum_congr rfl
  intro P hP
  have h := (mem_annularPrimeIdeals C a b x P).mp hP
  simp only [primeWeightTerm, h.1, h.2.1, and_self, ite_true]

theorem weightedPrimeSum_tendsto (C : Set (Ideal O)) {A : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeSum C W x)
      atTop (𝓝 (A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ))) := by
  obtain ⟨a, b, ha, hab, hsupp⟩ := exists_positive_support_annulus W hc hp
  apply (weightedPrimeAnnularSum_tendsto C hmass W hW ha hab.le hsupp).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [weightedPrimeSum_eq_annular C W ha hab.le hsupp hx]

def weightedPrimeSumDeleted (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ᶠ P : Ideal O, if P ∈ S then 0 else primeWeightTerm C W x P

theorem finite_prime_weights_eventually_zero (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) (hp : tsupport W ⊆ Set.Ioi 0) :
    ∀ᶠ x : ℝ in atTop, ∀ P ∈ S, primeWeightTerm C W x P = 0 := by
  have hz : ∀ᶠ y in 𝓝 (0 : ℝ), W y = 0 :=
    notMem_tsupport_iff_eventuallyEq.mp (fun h => (show (0 : ℝ) < 0 from hp h).false)
  rw [eventually_all_finset]
  intro P hP
  have ht : Tendsto (fun x : ℝ => (Ideal.absNorm P : ℝ) / x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      tendsto_inv_atTop_zero.const_mul (Ideal.absNorm P : ℝ)
  filter_upwards [ht hz] with x hx
  change W (Ideal.absNorm P / x) = 0 at hx
  simp only [primeWeightTerm, hx, zero_mul, ite_self]

theorem fixed_prime_deletion_eventually_eq (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) (hp : tsupport W ⊆ Set.Ioi 0) :
    weightedPrimeSumDeleted C S W =ᶠ[atTop] weightedPrimeSum C W := by
  filter_upwards [finite_prime_weights_eventually_zero C S W hp] with x hx
  unfold weightedPrimeSumDeleted weightedPrimeSum
  congr 1
  ext P
  by_cases hP : P ∈ S
  · simp only [hP, ite_true, hx P hP]
  · simp only [hP, ite_false]

theorem finite_prime_deleted_mass_eventually_zero (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) (hp : tsupport W ⊆ Set.Ioi 0) :
    ∀ᶠ x : ℝ in atTop, (∑ P ∈ S, primeWeightTerm C W x P) = 0 := by
  filter_upwards [finite_prime_weights_eventually_zero C S W hp] with x hx
  exact Finset.sum_eq_zero hx

theorem weightedPrimeSumDeleted_tendsto (C : Set (Ideal O)) (S : Finset (Ideal O)) {A : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeSumDeleted C S W x)
      atTop (𝓝 (A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ))) := by
  apply (weightedPrimeSum_tendsto C hmass W hW hc hp).congr'
  filter_upwards [fixed_prime_deletion_eventually_eq C S W hp] with x hx
  rw [hx]

theorem weightedPrimeSumDeleted_eq_annular (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hx : 0 < x) :
    weightedPrimeSumDeleted C S W x =
      ∑ P ∈ annularPrimeIdeals C a b x \ S,
        W (Ideal.absNorm P / x) * (Ideal.absNorm P : ℝ) ^ (-5 / 6 : ℝ) := by
  have hsub : Function.support (fun P => if P ∈ S then 0 else primeWeightTerm C W x P) ⊆
      (↑(annularPrimeIdeals C a b x \ S) : Set (Ideal O)) := by
    intro P hP
    change (if P ∈ S then 0 else primeWeightTerm C W x P) ≠ 0 at hP
    by_cases hPS : P ∈ S
    · simp only [hPS, ite_true, ne_self_iff_false] at hP
    · simp only [hPS, ite_false] at hP
      exact Finset.mem_sdiff.mpr ⟨primeWeightTerm_support_subset C W ha hab hsupp hx hP, hPS⟩
  rw [weightedPrimeSumDeleted, finsum_eq_finsetSum_of_support_subset _ hsub]
  apply Finset.sum_congr rfl
  intro P hP
  have hS := (Finset.mem_sdiff.mp hP).2
  have h := (mem_annularPrimeIdeals C a b x P).mp (Finset.mem_sdiff.mp hP).1
  simp only [hS, ite_false, primeWeightTerm, h.1, h.2.1, and_self, ite_true]

theorem powerWeight_integral_pos (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W)
    (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0)
    (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    0 < ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ) := by
  obtain ⟨a, b, ha, hab, hsupp⟩ := exists_positive_support_annulus W hc hp
  have hφ := contDiff_powerWeight W hW ha hsupp (-5 / 6)
  obtain ⟨y, hy⟩ : ∃ y : ℝ, W y ≠ 0 := by
    by_contra h
    push Not at h
    exact hWne (funext h)
  have hy0 : 0 < y := hp (subset_closure hy)
  apply hφ.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hc.mul_right
  · intro z
    by_cases hz : W z = 0
    · simp only [hz, zero_mul, Pi.zero_apply, le_refl]
    · have hz0 : 0 < z := hp (subset_closure hz)
      exact mul_nonneg (hW0 z) (Real.rpow_nonneg hz0.le _)
  · exact mul_ne_zero hy (Real.rpow_pos_of_pos hy0 _).ne'

theorem weightedPrimeSumDeleted_eventually_lower_bound (C : Set (Ideal O))
    (S : Finset (Ideal O)) {A : ℝ} (hA : 0 < A)
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c * x ^ (1 / 6 : ℝ) / Real.log x ≤ weightedPrimeSumDeleted C S W x := by
  let L : ℝ := A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ)
  have hL : 0 < L := mul_pos hA (powerWeight_integral_pos W hW hc hp hW0 hWne)
  refine ⟨L / 2, half_pos hL, ?_⟩
  have ht := weightedPrimeSumDeleted_tendsto C S hmass W hW hc hp
  have he := ht (Ioi_mem_nhds (half_lt_self hL))
  filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  change L / 2 < Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeSumDeleted C S W x at hx
  have hxp : 0 < x ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos (zero_lt_one.trans hx1) _
  apply (div_le_iff₀ (Real.log_pos hx1)).mpr
  have hmul := (le_div_iff₀ hxp).mp (show L / 2 ≤
      (Real.log x * weightedPrimeSumDeleted C S W x) / x ^ (1 / 6 : ℝ) by
    convert hx.le using 1; ring)
  nlinarith

theorem weightedPrimeSumDeleted_eventually_pos (C : Set (Ideal O))
    (S : Finset (Ideal O)) {A : ℝ} (hA : 0 < A)
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    ∀ᶠ x : ℝ in atTop, 0 < weightedPrimeSumDeleted C S W x := by
  obtain ⟨c, hc0, he⟩ := weightedPrimeSumDeleted_eventually_lower_bound C S hA hmass
    W hW hc hp hW0 hWne
  filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  exact (div_pos (mul_pos hc0 (Real.rpow_pos_of_pos (zero_lt_one.trans hx1) _))
    (Real.log_pos hx1)).trans_le hx

theorem weightedPrimeSum_nat_tendsto (C : Set (Ideal O)) {A : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) :
    Tendsto (fun N : ℕ => Real.log N / (N : ℝ) ^ (1 / 6 : ℝ) * weightedPrimeSum C W N)
      atTop (𝓝 (A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ))) :=
  (weightedPrimeSum_tendsto C hmass W hW hc hp).comp tendsto_natCast_atTop_atTop

end

end SevenEighths.PNT.AnnularPrimeMass

end OAI

end Source479
