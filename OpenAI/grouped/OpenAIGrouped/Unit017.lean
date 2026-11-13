import OpenAIGrouped.Unit016
import OpenAIGrouped.Unit009
import OpenAIGrouped.Unit013
import OpenAIGrouped.Unit008
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import OpenAIGrouped.Unit011
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Analytic.Order

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorProfilesBounds.lean; sha256: ae320323b2353a2580fdfd37f735a006b80cd7a0c9a929eb0f683c02a09ddf74 -/
section Source680
namespace OAI

namespace SevenEighths.HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

theorem scaled_derivatives_of_decay (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (L : ℝ) (hL : 0 ≤ L) (K : ℕ) (CF : ℝ) (hCF : 0 ≤ CF)
    (hdecay : ∀ i ≤ K, ∀ u : ℝ, 0 ≤ u →
      (1+u)^K*‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (fun z => F (R*Real.exp z)) y‖ ≤ C := by
  let m := Real.exp (-L)
  let H := Real.exp L
  let S : ℝ := ∑ j ∈ Finset.range (K+1), (j.factorial : ℝ)*CF*(H^2)^j
  have hm : 0 < m := Real.exp_pos _
  have hH : 1 ≤ H := Real.one_le_exp_iff.mpr hL
  have hS : 0 ≤ S := by dsimp [S]; positivity
  refine ⟨S/m^K,by positivity,?_⟩
  intro R hR j hj y hy
  have hh := FourierBridge.coupled_factor_uniform_derivative F R 1 y m H CF 0 K j hF
    hR hm (Real.exp_le_one_iff.mpr (by linarith)) hH (by simpa using hH)
    (Real.exp_le_exp.mpr (by simpa using (abs_le.mp hy).1))
    (Real.exp_le_exp.mpr (by simpa using (abs_le.mp hy).2))
    hj hCF (by simpa using hdecay)
  simp only [zero_add, pow_zero, mul_one, one_mul] at hh
  have hs : (j.factorial : ℝ)*CF*(H^2)^j ≤ S := by
    dsimp only [S]
    apply Finset.single_le_sum (s := Finset.range (K+1))
      (f := fun i => (i.factorial : ℝ)*CF*(H^2)^i) (a := j)
    · intro i hi; positivity
    · exact Finset.mem_range.mpr (by omega)
  exact (le_div_iff₀ (pow_pos hm K)).mpr (by simpa [mul_comm] using hh.trans hs)

theorem scaled_schwartz_derivatives (F : SchwartzMap ℝ ℂ)
    (L : ℝ) (hL : 0 ≤ L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (fun z => F (R*Real.exp z)) y‖ ≤ C := by
  apply scaled_derivatives_of_decay F (F.smooth ⊤) L hL K
    (FourierBridge.schwartzDerivativeDecayConstant F K K)
    (FourierBridge.schwartzDerivativeDecayConstant_nonneg F K K)
  intro i hi u hu
  simpa using FourierBridge.schwartz_derivative_decay_finite F 0 K K i u le_rfl hi hu

theorem scaled_expNeg_derivatives (L : ℝ) (hL : 0 ≤ L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (fun z => expNeg (R*Real.exp z)) y‖ ≤ C := by
  apply scaled_derivatives_of_decay expNeg expNeg_smooth L hL K
    ((K.factorial : ℝ)*Real.exp 1) (by positivity)
  intro i hi u hu
  exact expNeg_derivative_decay K i u hu

lemma const_one_derivative_norm (j : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ j (fun _ : ℝ => (1 : ℂ)) y‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_const]
  split_ifs <;> simp

lemma complement_derivative_bound (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (C : ℝ) (j : ℕ) (y : ℝ) (hbound : ‖iteratedFDeriv ℝ j F y‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (fun z => 1-F z) y‖ ≤ 1+C := by
  change ‖iteratedFDeriv ℝ j ((fun _ : ℝ => (1 : ℂ)) - F) y‖ ≤ _
  rw [iteratedFDeriv_sub contDiff_const (hF.of_le (by simp))]
  change ‖iteratedFDeriv ℝ j (fun _ : ℝ => (1 : ℂ)) y - iteratedFDeriv ℝ j F y‖ ≤ _
  exact (norm_sub_le _ _).trans (add_le_add (const_one_derivative_norm j y) hbound)

lemma product_derivative_bound (F G : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (CF CG : ℝ) (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (K j : ℕ) (hj : j ≤ K) (y : ℝ)
    (hFb : ∀ i ≤ K, ‖iteratedFDeriv ℝ i F y‖ ≤ CF)
    (hGb : ∀ i ≤ K, ‖iteratedFDeriv ℝ i G y‖ ≤ CG) :
    ‖iteratedFDeriv ℝ j (fun z => F z*G z) y‖ ≤ (2 : ℝ)^K*CF*CG := by
  apply (norm_iteratedFDeriv_mul_le hF hG y (n := j) (by simp)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ)*CF*CG := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ j := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hFb i (hi'.trans hj)) (by positivity))
        (hGb (j-i) ((Nat.sub_le j i).trans hj)) (norm_nonneg _) (by positivity)
    _ = (2 : ℝ)^j*CF*CG := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose j
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hCF) hCG

end
end SevenEighths.HeckeDetectorProfiles

end OAI

end Source680

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorProfilesUniform.lean; sha256: 7a386ddfd33ff9c8f8cd2dcbfb2b7c2b825d50591a59076a4f8892bab7540636 -/
section Source681
namespace OAI

namespace SevenEighths.HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

lemma logSource_support (Ω V T : ℝ → ℂ) (A B C : ℝ) :
    tsupport (logSourceFun Ω V T A B C) ⊆ tsupport Ω :=
  tsupport_mul_subset_left.trans (tsupport_mul_subset_left.trans tsupport_mul_subset_left)

theorem logSource_window_derivatives (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (logSourceFun Ω V T A B D) y‖ ≤ C := by
  obtain ⟨CΩ,hCΩ,hbΩ⟩ := hΩc.exists_bound_iteratedFDeriv hΩ K
  obtain ⟨CV,hCV,hbV⟩ := scaled_schwartz_derivatives V L hL K
  obtain ⟨CT,hCT,hbT⟩ := scaled_schwartz_derivatives T L hL K
  obtain ⟨CE,hCE,hbE⟩ := scaled_expNeg_derivatives L hL K
  let P := (2 : ℝ)^K
  refine ⟨P*(P*(P*CΩ*(1+CV))*CE)*CT,by dsimp [P]; positivity,?_⟩
  intro A B D hA hB hD j hj y hy
  let v : ℝ → ℂ := fun z => V (A*Real.exp z)
  let e : ℝ → ℂ := fun z => expNeg (B*Real.exp z)
  let t : ℝ → ℂ := fun z => T (D*Real.exp z)
  have hv : ContDiff ℝ ∞ v := (V.smooth ⊤).comp (by fun_prop)
  have he : ContDiff ℝ ∞ e := expNeg_smooth.comp (by fun_prop)
  have ht : ContDiff ℝ ∞ t := (T.smooth ⊤).comp (by fun_prop)
  have hcv : ContDiff ℝ ∞ (fun z => 1-v z) := contDiff_const.sub hv
  have hcomp (i : ℕ) (hi : i ≤ K) : ‖iteratedFDeriv ℝ i (fun z => 1-v z) y‖ ≤ 1+CV :=
    complement_derivative_bound v hv CV i y (hbV A hA i hi y hy)
  have hfirst (i : ℕ) (hi : i ≤ K) :
      ‖iteratedFDeriv ℝ i (fun z => Ω z*(1-v z)) y‖ ≤ P*CΩ*(1+CV) :=
    product_derivative_bound Ω _ hΩ hcv CΩ (1+CV) hCΩ (by positivity) K i hi y
      (fun q hq => hbΩ q hq y) hcomp
  have hsecond (i : ℕ) (hi : i ≤ K) :
      ‖iteratedFDeriv ℝ i (fun z => Ω z*(1-v z)*e z) y‖ ≤ P*(P*CΩ*(1+CV))*CE :=
    product_derivative_bound _ e (hΩ.mul hcv) he _ CE (by dsimp [P]; positivity) hCE
      K i hi y hfirst (fun q hq => hbE B hB q hq y hy)
  exact product_derivative_bound _ t ((hΩ.mul hcv).mul he) ht _ CT
    (by dsimp [P]; positivity) hCT K j hj y hsecond (fun q hq => hbT D hD q hq y hy)

theorem logSource_uniform_seminorm (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      ∀ k j : ℕ, j ≤ K →
      SchwartzMap.seminorm ℝ k j (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D)
        ≤ L^k*C := by
  obtain ⟨C,hC,hb⟩ := logSource_window_derivatives Ω V T hΩc hΩ L hL K
  refine ⟨C,hC,?_⟩
  intro A B D hA hB hD k j hj
  apply SchwartzMap.seminorm_le_bound' ℝ k j _ (by positivity)
  intro y
  change ‖y‖^k*‖iteratedDeriv j (logSourceFun Ω V T A B D) y‖ ≤ L^k*C
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hz : ‖iteratedFDeriv ℝ j (logSourceFun Ω V T A B D) y‖ = 0
  · rw [hz, mul_zero]; positivity
  have hys : y ∈ tsupport Ω := logSource_support Ω V T A B D
    ((support_iteratedFDeriv_subset j) (by simpa [Function.mem_support] using hz))
  have hy : |y| ≤ L := abs_le.mpr (hwindow hys)
  exact mul_le_mul (by simpa [Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg y) hy k)
    (hb A B D hA hB hD j hj y hy) (norm_nonneg _) (pow_nonneg hL k)

end
end SevenEighths.HeckeDetectorProfiles

end OAI

end Source681

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorFourier.lean; sha256: 3cfebeba1b243d97e149968ea3aabefc62996c0751c1275580a2875dda9a7867 -/
section Source682
namespace OAI

namespace SevenEighths.HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
open HeckeDetectorProfiles
noncomputable section

theorem uniform_fourier_moment (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      (∫ t : ℝ, (1+‖t‖)^J *
        ‖(𝓕 (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D)) t‖) ≤ C := by
  let p := (volume : Measure ℝ).integrablePower
  obtain ⟨C,hC,hb⟩ := logSource_uniform_seminorm Ω V T hΩc hΩ L hL hwindow (J+p)
  let C' := (1+L^p)*C
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  refine ⟨(2 : ℝ)^J*(FourierBridge.coefficientMomentBound 0 C'+
    FourierBridge.coefficientMomentBound J C'),?_,?_⟩
  · exact mul_nonneg (by positivity) (add_nonneg
      (FourierBridge.coefficientMomentBound_nonneg 0 C' hC')
      (FourierBridge.coefficientMomentBound_nonneg J C' hC'))
  intro A B D hA hB hD
  have hh := FourierBridge.uniform_fourier_one_plus_moment
    (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D) J 1 C'
    (by norm_num) hC' (by
      intro i hi
      have h0 := hb A B D hA hB hD 0 i hi
      have hp := hb A B D hA hB hD p i hi
      simp only [pow_zero, one_mul] at h0 ⊢
      dsimp only [C']
      linarith)
  simpa only [one_mul] using hh

theorem schwartz_weighted_tail (g : SchwartzMap ℝ ℂ) (J N : ℕ)
    (R : ℝ) (hR : 0 < R) :
    R^N*(∫ t : ℝ in {t | R < ‖t‖}, (1+‖t‖)^J*‖(𝓕 g) t‖) ≤
      ∫ t : ℝ, (1+‖t‖)^(J+N)*‖(𝓕 g) t‖ := by
  have hiJ := AnalyticBridge.schwartz_fourier_one_plus_integrable g J
  have hiN := AnalyticBridge.schwartz_fourier_one_plus_integrable g (J+N)
  have hs : MeasurableSet {t : ℝ | R < ‖t‖} := measurableSet_lt measurable_const continuous_norm.measurable
  rw [← integral_const_mul]
  apply (setIntegral_mono_on (hiJ.const_mul _).integrableOn hiN.integrableOn hs ?_).trans
    (setIntegral_le_integral hiN (Filter.Eventually.of_forall (by intro t; positivity)))
  intro t ht
  have hp : R^N ≤ (1+‖t‖)^N := pow_le_pow_left₀ hR.le (by change R < ‖t‖ at ht; linarith) N
  calc
    _ ≤ (1+‖t‖)^N*((1+‖t‖)^J*‖(𝓕 g) t‖) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem uniform_fourier_tail (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (J N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      ∀ R : ℝ, 0 < R →
      (∫ t : ℝ in {t | R < ‖t‖}, (1+‖t‖)^J *
        ‖(𝓕 (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D)) t‖) ≤ C/R^N := by
  obtain ⟨C,hC,hb⟩ := uniform_fourier_moment Ω V T hΩc hΩ L hL hwindow (J+N)
  refine ⟨C,hC,?_⟩
  intro A B D hA hB hD R hR
  apply (le_div_iff₀ (pow_pos hR N)).mpr
  simpa [mul_comm] using (schwartz_weighted_tail
    (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D) J N R hR).trans
    (hb A B D hA hB hD)

theorem logSource_product_inversion (Ω V T : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (hV : ContDiff ℝ ∞ V) (hT : ContDiff ℝ ∞ T)
    (A B D x y : ℝ) :
    logSourceFun Ω V T A B D (x+y) =
      ∫ t : ℝ, FourierBridge.logPhase t x * FourierBridge.logPhase t y *
        (𝓕 (logSource Ω V T hΩc hΩ hV hT A B D)) t := by
  have hh := FourierBridge.schwartz_log_inversion
    (logSource Ω V T hΩc hΩ hV hT A B D) (x+y)
  change logSourceFun Ω V T A B D (x+y) = _ at hh
  rw [hh]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [← FourierBridge.logPhase_add]
  congr 1
  simp only [FourierBridge.logPhase, RCLike.inner_apply, conj_trivial]
  congr 2
  ring_nf

end
end SevenEighths.HeckeDetectorFourier

end OAI

end Source682

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorFourierSeparation.lean; sha256: 3be7de3dea3a5f4318df2ccbfb87492ac0b0baa2929b33613507133e92e6cd69 -/
section Source683
namespace OAI

namespace SevenEighths.HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

def phasePolynomial {α : Type*} (S : Finset α) (a : α → ℂ) (x : α → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ S, a i*FourierBridge.logPhase t (x i)

lemma phasePolynomial_continuous {α : Type*} (S : Finset α) (a : α → ℂ) (x : α → ℝ) :
    Continuous (phasePolynomial S a x) := by
  apply continuous_finsetSum
  intro i hi
  exact continuous_const.mul (FourierBridge.logPhase_continuous_left _)

lemma phasePolynomial_norm {α : Type*} (S : Finset α) (a : α → ℂ) (x : α → ℝ) (t : ℝ) :
    ‖phasePolynomial S a x t‖ ≤ ∑ i ∈ S, ‖a i‖ := by
  calc
    _ ≤ ∑ i ∈ S, ‖a i*FourierBridge.logPhase t (x i)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, FourierBridge.logPhase_norm, mul_one]

lemma separated_pair_integrable {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ) (g : SchwartzMap ℝ ℂ) :
    Integrable (fun t => (𝓕 g) t*phasePolynomial S a x t*phasePolynomial T b y t) := by
  have hmeas : AEStronglyMeasurable (fun t => phasePolynomial S a x t*phasePolynomial T b y t) volume :=
    ((phasePolynomial_continuous S a x).mul
    (phasePolynomial_continuous T b y)).aestronglyMeasurable
  have hh := (𝓕 g).integrable.mul_bdd hmeas (Filter.Eventually.of_forall (fun t =>
    (norm_mul _ _).le.trans (mul_le_mul (phasePolynomial_norm S a x t)
      (phasePolynomial_norm T b y t) (norm_nonneg _) (Finset.sum_nonneg (fun i hi => norm_nonneg _)))))
  simpa only [mul_assoc] using hh

lemma schwartz_product_inversion (g : SchwartzMap ℝ ℂ) (x y : ℝ) :
    g (x+y) = ∫ t : ℝ,
      (𝓕 g) t*FourierBridge.logPhase t x*FourierBridge.logPhase t y := by
  rw [FourierBridge.schwartz_log_inversion g (x+y)]
  apply integral_congr_ae
  filter_upwards [] with t
  have hp : Complex.exp (↑(2*Real.pi*inner ℝ t (x+y))*Complex.I) =
      FourierBridge.logPhase t x*FourierBridge.logPhase t y := by
    rw [← FourierBridge.logPhase_add]
    simp only [FourierBridge.logPhase, RCLike.inner_apply, conj_trivial]
    congr 2
    ring_nf
  rw [hp]
  ring

theorem finite_pair_separation {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ) (g : SchwartzMap ℝ ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, a i*b j*g (x i+y j)) =
      ∫ t : ℝ, (𝓕 g) t*phasePolynomial S a x t*phasePolynomial T b y t := by
  have hterm (i : α) (j : β) : Integrable (fun t : ℝ =>
      (𝓕 g) t*(a i*FourierBridge.logPhase t (x i))*(b j*FourierBridge.logPhase t (y j))) := by
    simpa only [phasePolynomial, Finset.sum_singleton] using
      separated_pair_integrable {i} {j} a b x y g
  have hsum (t : ℝ) : (𝓕 g) t*phasePolynomial S a x t*phasePolynomial T b y t =
      ∑ i ∈ S, ∑ j ∈ T,
        (𝓕 g) t*(a i*FourierBridge.logPhase t (x i))*(b j*FourierBridge.logPhase t (y j)) := by
    simp only [phasePolynomial, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_comm
  simp_rw [hsum]
  rw [integral_finsetSum S (fun i hi => integrable_finsetSum T (fun j hj => hterm i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum T (fun j hj => hterm i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [schwartz_product_inversion g (x i) (y j), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  ring

end
end SevenEighths.HeckeDetectorFourier

end OAI

end Source683

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorFourierWitness.lean; sha256: 0626b78ba8177f8bb6750821c9ee33f403d3e7b62d08ea7b1e26a83783e246a7 -/
section Source684
namespace OAI

namespace SevenEighths.HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

lemma frequency_interval_compl (R : ℝ) :
    (Set.Icc (-R) R)ᶜ = {t : ℝ | R < ‖t‖} := by
  ext t
  simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_ofPred_eq, Real.norm_eq_abs,
    ← abs_le, not_le]

private lemma exists_interval_norm_product (f h : ℝ → ℂ) (hf : Continuous f)
    (hh : Integrable h) (hprod : Integrable (fun u => h u * f u))
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ t : ℝ, ‖t‖ ≤ R ∧
      ‖∫ u : ℝ in Set.Icc (-R) R, h u * f u‖ ≤ (∫ u : ℝ, ‖h u‖) * ‖f t‖ := by
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc (-R) R).Nonempty from ⟨0, by constructor <;> linarith⟩)
    hf.norm.continuousOn
  refine ⟨t, by simpa only [Real.norm_eq_abs, abs_le, Set.mem_Icc] using ht, ?_⟩
  have hb : Integrable (fun u => ‖h u‖ * ‖f t‖) := hh.norm.mul_const _
  calc
    _ ≤ ∫ u : ℝ in Set.Icc (-R) R, ‖h u * f u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in Set.Icc (-R) R, ‖h u‖ * ‖f t‖ := by
      apply setIntegral_mono_on hprod.norm.integrableOn hb.integrableOn measurableSet_Icc
      intro u hu
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hmax hu) (norm_nonneg _)
    _ ≤ ∫ u : ℝ, ‖h u‖ * ‖f t‖ :=
      setIntegral_le_integral hb (Filter.Eventually.of_forall (by intro u; positivity))
    _ = _ := integral_mul_const _ _

theorem exists_interval_frequency {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ)
    (g : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ t : ℝ, ‖t‖ ≤ R ∧
      ‖∫ u : ℝ in Set.Icc (-R) R,
        (𝓕 g) u*phasePolynomial S a x u*phasePolynomial T b y u‖ ≤
        (∫ u : ℝ, ‖(𝓕 g) u‖)*
          ‖phasePolynomial S a x t*phasePolynomial T b y t‖ := by
  have hf : Continuous (fun u => phasePolynomial S a x u * phasePolynomial T b y u) :=
    (phasePolynomial_continuous S a x).mul (phasePolynomial_continuous T b y)
  have hi : Integrable (fun u => (𝓕 g) u *
      (phasePolynomial S a x u * phasePolynomial T b y u)) := by
    simpa only [mul_assoc] using separated_pair_integrable S T a b x y g
  obtain ⟨t, ht, hb⟩ := exists_interval_norm_product
    (fun u => phasePolynomial S a x u * phasePolynomial T b y u)
    (fun u => (𝓕 g) u) hf (𝓕 g).integrable hi R hR
  exact ⟨t, ht, by simpa only [mul_assoc] using hb⟩

private theorem integral_sub_interval_norm_le (f w : ℝ → ℂ) (E R : ℝ)
    (hf : Integrable f) (hw : Integrable w)
    (hbound : ∀ u, ‖f u‖ ≤ E * ‖w u‖) :
    ‖(∫ u : ℝ, f u) - (∫ u : ℝ in Set.Icc (-R) R, f u)‖ ≤
      E * (∫ u : ℝ in {u | R < ‖u‖}, ‖w u‖) := by
  have hsplit := integral_add_compl (s := Set.Icc (-R) R) measurableSet_Icc hf
  have heq : (∫ u : ℝ, f u) - (∫ u : ℝ in Set.Icc (-R) R, f u) =
      ∫ u : ℝ in {u | R < ‖u‖}, f u := by
    rw [← hsplit, frequency_interval_compl]
    abel
  rw [heq]
  have hm : MeasurableSet {u : ℝ | R < ‖u‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  calc
    _ ≤ ∫ u : ℝ in {u | R < ‖u‖}, ‖f u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in {u | R < ‖u‖}, E * ‖w u‖ :=
      setIntegral_mono_on hf.norm.integrableOn (hw.norm.const_mul E).integrableOn hm
        (fun u _ => hbound u)
    _ = _ := integral_const_mul _ _

private theorem separated_pair_norm_le {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ) (z : ℂ) (u : ℝ) :
    ‖z * phasePolynomial S a x u * phasePolynomial T b y u‖ ≤
      ((∑ i ∈ S, ‖a i‖) * (∑ j ∈ T, ‖b j‖)) * ‖z‖ := by
  rw [mul_assoc, norm_mul, norm_mul, mul_comm ‖z‖]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
  exact mul_le_mul (phasePolynomial_norm S a x u) (phasePolynomial_norm T b y u)
    (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

private theorem schwartz_tail_le (g : SchwartzMap ℝ ℂ) (R : ℝ)
    (hR : 0 < R) (N : ℕ) :
    (∫ u : ℝ in {u | R < ‖u‖}, ‖(𝓕 g) u‖) ≤
      (∫ u : ℝ, (1+‖u‖)^N * ‖(𝓕 g) u‖) / R^N := by
  apply (le_div_iff₀ (pow_pos hR N)).mpr
  simpa only [pow_zero, one_mul, Nat.zero_add, mul_comm] using
    schwartz_weighted_tail g 0 N R hR

private theorem separated_pair_tail_of_bound {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ)
    (w : ℝ → ℂ) (R M : ℝ) (N : ℕ)
    (hi : Integrable (fun u => w u * phasePolynomial S a x u * phasePolynomial T b y u))
    (hw : Integrable w) (hbound : (∫ u : ℝ in {u | R < ‖u‖}, ‖w u‖) ≤ M / R^N) :
    ‖(∫ u : ℝ, w u * phasePolynomial S a x u * phasePolynomial T b y u) -
      (∫ u : ℝ in Set.Icc (-R) R,
        w u * phasePolynomial S a x u * phasePolynomial T b y u)‖ ≤
      ((∑ i ∈ S, ‖a i‖) * (∑ j ∈ T, ‖b j‖)) / R^N * M := by
  let E := (∑ i ∈ S, ‖a i‖) * (∑ j ∈ T, ‖b j‖)
  have hE : 0 ≤ E := mul_nonneg
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have htail := integral_sub_interval_norm_le
    (fun u => w u * phasePolynomial S a x u * phasePolynomial T b y u)
    w E R hi hw (fun u => separated_pair_norm_le S T a b x y (w u) u)
  calc
    _ ≤ E * (∫ u : ℝ in {u | R < ‖u‖}, ‖w u‖) := htail
    _ ≤ E * (M / R^N) := mul_le_mul_of_nonneg_left hbound hE
    _ = _ := by rw [div_mul_eq_mul_div, mul_div_assoc]

theorem separated_pair_tail {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ)
    (g : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0 < R) (N : ℕ) :
    ‖(∫ u : ℝ, (𝓕 g) u*phasePolynomial S a x u*phasePolynomial T b y u) -
      (∫ u : ℝ in Set.Icc (-R) R,
        (𝓕 g) u*phasePolynomial S a x u*phasePolynomial T b y u)‖ ≤
      ((∑ i ∈ S, ‖a i‖)*(∑ j ∈ T, ‖b j‖))/R^N *
        (∫ u : ℝ, (1+‖u‖)^N*‖(𝓕 g) u‖) := by
  exact separated_pair_tail_of_bound S T a b x y (fun u : ℝ => (𝓕 g : SchwartzMap ℝ ℂ) u)
    R (∫ u : ℝ, (1+‖u‖)^N * ‖(𝓕 g) u‖) N
    (separated_pair_integrable S T a b x y g) (𝓕 g).integrable
    (schwartz_tail_le g R hR N)

theorem exists_bounded_frequency {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ)
    (g : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0 < R) (N : ℕ) :
    ∃ t : ℝ, ‖t‖ ≤ R ∧
      ‖∑ i ∈ S, ∑ j ∈ T, a i*b j*g (x i+y j)‖ ≤
      ((∑ i ∈ S, ‖a i‖)*(∑ j ∈ T, ‖b j‖))/R^N *
        (∫ u : ℝ, (1+‖u‖)^N*‖(𝓕 g) u‖) +
      (∫ u : ℝ, ‖(𝓕 g) u‖)*
        ‖phasePolynomial S a x t*phasePolynomial T b y t‖ := by
  obtain ⟨t,ht,hb⟩ := exists_interval_frequency S T a b x y g R hR.le
  refine ⟨t,ht,?_⟩
  rw [finite_pair_separation]
  have htail := separated_pair_tail S T a b x y g R hR N
  exact (norm_le_norm_sub_add _ _).trans (add_le_add htail hb)

end
end SevenEighths.HeckeDetectorFourier

end OAI

end Source684

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorWitnessArithmetic.lean; sha256: b63baaac3d06b4e8d37fe2dc5b25ba228025d1b90111429ecc68c747b42d6559 -/
section Source685
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorWitnessArithmetic
open HeckeFamily UniqueFactorizationMonoid CompletedGauss
local notation "O" => HeckeFamily.O

def cutoffCoefficient (V : ℝ → ℂ) (D : ℝ) (I : Ideal O) : ℂ :=
  if I = 0 then 0 else
    ∑' p : MulFiber I, (moebius p.val.1 : ℂ) * V ((Ideal.absNorm p.val.1 : ℝ) / D)

theorem fiber_norm_le {I : Ideal O} (hI : I ≠ 0) (p : MulFiber I) :
    Ideal.absNorm p.val.1 ≤ Ideal.absNorm I := by
  apply Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
  exact map_dvd Ideal.absNorm ⟨p.val.2, p.property.symm⟩

theorem cutoffCoefficient_small (V : ℝ → ℂ) (D : ℝ) (hD : 0 < D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (I : Ideal O) (hI : (Ideal.absNorm I : ℝ) ≤ D) :
    cutoffCoefficient V D I = if I = 1 then 1 else 0 := by
  by_cases hI0 : I = 0
  · simp [cutoffCoefficient, hI0]
  · rw [cutoffCoefficient, ite_eq_right hI0]
    have heq : (fun p : MulFiber I => (moebius p.val.1 : ℂ) * V ((Ideal.absNorm p.val.1 : ℝ) / D)) =
        (fun p : MulFiber I => (moebius p.val.1 : ℂ)) := by
      funext p
      rw [hV _ (div_nonneg (by positivity) hD.le) ((div_le_one hD).mpr ?_), mul_one]
      exact (by exact_mod_cast fiber_norm_le hI0 p : (Ideal.absNorm p.val.1 : ℝ) ≤ Ideal.absNorm I).trans hI
    rw [heq]
    exact mulFiber_moebius_sum I hI0

theorem cutoffCoefficient_tail (V : ℝ → ℂ) (D : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (I : Ideal O) :
    cutoffCoefficient V D I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D)) =
      cutoffCoefficient V D I - if I = 1 then 1 else 0 := by
  have hD0 : 0 < D := by linarith
  by_cases hI : (Ideal.absNorm I : ℝ) ≤ D
  · rw [cutoffCoefficient_small V D hD0 hV I hI]
    by_cases hI1 : I = 1
    · subst I
      simp only [map_one, Nat.cast_one, mul_one, ite_true, one_mul, sub_self]
      rw [hV _ (by positivity) ((div_le_one hD0).mpr hD), sub_self]
    · simp only [hI1, ite_false, zero_mul, sub_zero]
  · have hv : V (2 * (Ideal.absNorm I : ℝ) / D) = 0 := by
      apply hVzero
      apply (le_div_iff₀ hD0).mpr
      linarith [lt_of_not_ge hI]
    have hI1 : I ≠ 1 := by
      intro hh
      subst I
      simp only [map_one, Nat.cast_one] at hI
      linarith
    rw [hv, sub_zero, mul_one, ite_eq_right hI1, sub_zero]

theorem weighted_fiber (χ : Character) (V : ℝ → ℂ) (D : ℝ) (s : ℂ) (I : Ideal O) :
    (∑' p : MulFiber I, (moebius p.val.1 : ℂ) * V ((Ideal.absNorm p.val.1 : ℝ) / D) *
      IdealEuler.weighted (idealCoeff χ) s (p.val.1 * p.val.2)) =
      cutoffCoefficient V D I * IdealEuler.weighted (idealCoeff χ) s I := by
  by_cases hI : I = 0
  · subst I
    have hz (p : MulFiber 0) : IdealEuler.weighted (idealCoeff χ) s (p.val.1 * p.val.2) = 0 := by
      rw [p.property, map_zero]
    simp [hz, cutoffCoefficient]
  · rw [cutoffCoefficient, ite_eq_right hI, ← tsum_mul_right]
    apply tsum_congr
    intro p
    rw [p.property]

def exponentialTerm (χ : Character) (V : ℝ → ℂ) (D : ℝ) (s : ℂ) (Y : ℝ) (I : Ideal O) : ℂ :=
  cutoffCoefficient V D I * IdealEuler.weighted (idealCoeff χ) s I *
    Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ) / (Y : ℂ))

theorem exponentialTerm_tail (χ : Character) (V : ℝ → ℂ) (D : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (Y : ℝ) (I : Ideal O) :
    exponentialTerm χ V D s Y I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D)) =
      exponentialTerm χ V D s Y I - if I = 1 then Complex.exp (-1 / (Y : ℂ)) else 0 := by
  have h := cutoffCoefficient_tail V D hD hV hVzero I
  unfold exponentialTerm
  calc
    _ = (cutoffCoefficient V D I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D))) *
        IdealEuler.weighted (idealCoeff χ) s I * Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ) / (Y : ℂ)) := by ring
    _ = _ := by
      rw [h]
      by_cases hI : I = 1
      · subst I
        simp only [ite_true, map_one, Nat.cast_one, Complex.ofReal_one, mul_one]
        ring
      · simp only [hI, ite_false, sub_zero]

theorem exponential_sum_tail (χ : Character) (V : ℝ → ℂ) (D : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (Y : ℝ)
    (hsum : Summable (exponentialTerm χ V D s Y)) :
    (∑' I : Ideal O, exponentialTerm χ V D s Y I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D))) =
      (∑' I : Ideal O, exponentialTerm χ V D s Y I) - Complex.exp (-1 / (Y : ℂ)) := by
  simp_rw [exponentialTerm_tail χ V D hD hV hVzero s Y]
  rw [hsum.tsum_sub ((hasSum_ite_eq (1 : Ideal O) (Complex.exp (-1 / (Y : ℂ)))).summable)]
  simp only [tsum_ite_eq]

end SevenEighths.HeckeDetectorWitnessArithmetic

end

end OAI

end Source685

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorPartition.lean; sha256: 32ac0a12ece8c986c2630603dee97493f864a42b0c4922eee5e14d8a13d2f4a2 -/
section Source686
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.HeckeDetectorPartition
open DyadicTransfer

theorem partition (V : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (n J : ℕ) (hn : 1 ≤ n) (hJ : (n : ℝ) ≤ (2 : ℝ)^J) :
    (∑ j ∈ Finset.range (J+1), annularCutoff V ((n : ℝ)/(2 : ℝ)^j)) = 1 := by
  rw [partial_partition]
  rw [hsmall _ (by positivity) ((div_le_one (by positivity)).mpr hJ)]
  rw [hlarge _ (by exact_mod_cast (show 2 ≤ 2*n by omega))]
  ring

theorem finite_pair_reassembly {A : Type*} (S : Finset A) (a : A → ℂ)
    (n m : A → ℕ) (V : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (J K : ℕ)
    (hn : ∀ p ∈ S, 1 ≤ n p ∧ (n p : ℝ) ≤ (2 : ℝ)^J)
    (hm : ∀ p ∈ S, 1 ≤ m p ∧ (m p : ℝ) ≤ (2 : ℝ)^K) :
    (∑ p ∈ S, a p) =
      ∑ j ∈ Finset.range (J+1), ∑ k ∈ Finset.range (K+1), ∑ p ∈ S,
        a p * annularCutoff V ((n p : ℝ)/(2 : ℝ)^j) *
          annularCutoff V ((m p : ℝ)/(2 : ℝ)^k) := by
  symm
  calc
    _ = ∑ p ∈ S, ∑ j ∈ Finset.range (J+1), ∑ k ∈ Finset.range (K+1),
        a p * annularCutoff V ((n p : ℝ)/(2 : ℝ)^j) *
          annularCutoff V ((m p : ℝ)/(2 : ℝ)^k) := by
      calc
        _ = ∑ j ∈ Finset.range (J+1), ∑ p ∈ S, ∑ k ∈ Finset.range (K+1),
            a p * annularCutoff V ((n p : ℝ)/(2 : ℝ)^j) *
              annularCutoff V ((m p : ℝ)/(2 : ℝ)^k) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      simp_rw [← Finset.mul_sum]
      rw [partition V hsmall hlarge (m p) K (hm p hp).1 (hm p hp).2]
      simp only [mul_one]
      rw [← Finset.mul_sum, partition V hsmall hlarge (n p) J (hn p hp).1 (hn p hp).2,
        mul_one]

theorem annular_support (V : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (x : ℝ) (hx : 0 ≤ x) (j : ℕ)
    (hne : annularCutoff V (x/(2 : ℝ)^j) ≠ 0) :
    (2 : ℝ)^j / 2 < x ∧ x < 2*(2 : ℝ)^j := by
  have hp : 0 < (2 : ℝ)^j := by positivity
  have hy : 0 ≤ x/(2 : ℝ)^j := div_nonneg hx hp.le
  have hlo : 1/2 < x/(2 : ℝ)^j := by
    by_contra h
    have hh := le_of_not_gt h
    apply hne
    rw [annularCutoff, hsmall _ hy (by linarith), hsmall _ (by positivity) (by linarith)]
    ring
  have hhi : x/(2 : ℝ)^j < 2 := by
    by_contra h
    apply hne
    exact annularCutoff_eq_zero_of_two_le V hlarge (le_of_not_gt h)
  constructor
  · have := (lt_div_iff₀ hp).mp hlo
    linarith
  · exact (div_lt_iff₀ hp).mp hhi

def length (X : ℝ) : ℕ := ⌈Real.logb 2 X⌉₊

theorem norm_le_last_scale (X : ℝ) (hX : 0 < X) : X ≤ (2 : ℝ)^(length X) := by
  have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hX).mp
    (Nat.le_ceil (Real.logb 2 X))
  simpa only [Real.rpow_natCast, length] using h

theorem length_bound (X : ℝ) (hX : 1 ≤ X) :
    (length X : ℝ) + 1 < Real.logb 2 X + 2 := by
  have hlog : 0 ≤ Real.logb 2 X := Real.logb_nonneg (by norm_num) hX
  have h := Nat.ceil_lt_add_one hlog
  change (⌈Real.logb 2 X⌉₊ : ℝ) + 1 < _
  linarith

theorem pair_scale_bounds (V T : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (hterm : ∀ y : ℝ, 2 ≤ y → T y = 0)
    (x y D U : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hD : 0 < D) (hU : 0 < U)
    (j k : ℕ)
    (hj : annularCutoff V (x/(2 : ℝ)^j) ≠ 0)
    (hk : annularCutoff V (y/(2 : ℝ)^k) ≠ 0)
    (hfirst : V (x/D) ≠ 0)
    (hproduct : 1 - V (2*(x*y)/D) ≠ 0)
    (hterminal : T (x*y/U) ≠ 0) :
    (2 : ℝ)^j < 4*D ∧ D/8 < (2 : ℝ)^j*(2 : ℝ)^k ∧
      (2 : ℝ)^j*(2 : ℝ)^k < 8*U := by
  obtain ⟨hjlo,hjhi⟩ := annular_support V hsmall hlarge x hx j hj
  obtain ⟨hklo,hkhi⟩ := annular_support V hsmall hlarge y hy k hk
  have hJ : 0 < (2 : ℝ)^j := by positivity
  have hK : 0 < (2 : ℝ)^k := by positivity
  have hxd : x < 2*D := by
    by_contra h
    apply hfirst
    apply hlarge
    exact (le_div_iff₀ hD).mpr (le_of_not_gt h)
  have hprod : D < 2*(x*y) := by
    by_contra h
    apply hproduct
    rw [hsmall _ (by positivity) ((div_le_one hD).mpr (le_of_not_gt h))]
    ring
  have hxyU : x*y < 2*U := by
    by_contra h
    apply hterminal
    apply hterm
    exact (le_div_iff₀ hU).mpr (le_of_not_gt h)
  have hlo : (2 : ℝ)^j*(2 : ℝ)^k/4 < x*y := by
    have h1 := mul_lt_mul_of_pos_right hjlo (show 0 < y by linarith)
    have h2 := mul_lt_mul_of_pos_left hklo (show 0 < (2 : ℝ)^j/2 by positivity)
    nlinarith
  have hhi : x*y < 4*((2 : ℝ)^j*(2 : ℝ)^k) := by
    have h1 := mul_lt_mul_of_pos_right hjhi (show 0 < y by linarith)
    have h2 := mul_lt_mul_of_pos_left hkhi (show 0 < 2*(2 : ℝ)^j by positivity)
    nlinarith
  constructor
  · linarith
  constructor <;> linarith

def pairCoefficient (χ : HeckeFamily.Character) (V T : ℝ → ℂ)
    (D Y U : ℝ) (s : ℂ) (p : Ideal HeckeFamily.O × Ideal HeckeFamily.O) : ℂ :=
  (UniqueFactorizationMonoid.moebius p.1 : ℂ) * V ((Ideal.absNorm p.1 : ℝ)/D) *
    IdealEuler.weighted (HeckeFamily.idealCoeff χ) s (p.1*p.2) *
    Complex.exp (-((Ideal.absNorm (p.1*p.2) : ℝ) : ℂ)/(Y : ℂ)) *
    (1-V (2*(Ideal.absNorm (p.1*p.2) : ℝ)/D)) * T ((Ideal.absNorm (p.1*p.2) : ℝ)/U)

theorem actual_pair_reassembly (χ : HeckeFamily.Character) (V T : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (D Y U X Z : ℝ) (hX : 0 < X) (hZ : 0 < Z) (s : ℂ)
    (S : Finset (Ideal HeckeFamily.O × Ideal HeckeFamily.O))
    (hS : ∀ p ∈ S, p.1 ≠ 0 ∧ p.2 ≠ 0 ∧
      (Ideal.absNorm p.1 : ℝ) ≤ X ∧ (Ideal.absNorm p.2 : ℝ) ≤ Z) :
    (∑ p ∈ S, pairCoefficient χ V T D Y U s p) =
      ∑ j ∈ Finset.range (length X+1), ∑ k ∈ Finset.range (length Z+1), ∑ p ∈ S,
        pairCoefficient χ V T D Y U s p *
          annularCutoff V ((Ideal.absNorm p.1 : ℝ)/(2 : ℝ)^j) *
          annularCutoff V ((Ideal.absNorm p.2 : ℝ)/(2 : ℝ)^k) := by
  apply finite_pair_reassembly S _ _ _ V hsmall hlarge
  · intro p hp
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hS p hp).1),
      (hS p hp).2.2.1.trans (norm_le_last_scale X hX)⟩
  · intro p hp
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hS p hp).2.1),
      (hS p hp).2.2.2.trans (norm_le_last_scale Z hZ)⟩

theorem exists_large_pair (J K : ℕ) (F : ℕ → ℕ → ℂ) :
    ∃ j ∈ Finset.range (J+1), ∃ k ∈ Finset.range (K+1),
      ‖∑ j ∈ Finset.range (J+1), ∑ k ∈ Finset.range (K+1), F j k‖ ≤
        ((J+1 : ℕ) : ℝ)*((K+1 : ℕ) : ℝ)*‖F j k‖ := by
  let S := (Finset.range (J+1)) ×ˢ (Finset.range (K+1))
  have hS : S.Nonempty := ⟨(0,0), by simp [S]⟩
  obtain ⟨p,hp,hmax⟩ := S.exists_max_image (fun p => ‖F p.1 p.2‖) hS
  obtain ⟨hj,hk⟩ := Finset.mem_product.mp hp
  refine ⟨p.1,hj,p.2,hk,?_⟩
  calc
    _ = ‖∑ q ∈ S, F q.1 q.2‖ := by rw [Finset.sum_product]
    _ ≤ ∑ q ∈ S, ‖F q.1 q.2‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ S, ‖F p.1 p.2‖ := Finset.sum_le_sum (fun q hq => hmax q hq)
    _ = _ := by simp [S, Finset.card_product, mul_assoc]

end SevenEighths.HeckeDetectorPartition

end

end OAI

end Source686

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorFourierActual.lean; sha256: 651411ebbda4d602cdf7ca86a7bde2f5e99aadbc9edb5453341c2b833e3c9f7d -/
section Source687
namespace OAI

namespace SevenEighths.HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
open HeckeFamily HeckeDetectorProfiles
noncomputable section

def inverseCoefficient (χ : Character) (V W : ℝ → ℂ) (Dstar D : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius I : ℂ)*IdealEuler.weighted (idealCoeff χ) s I*
    V ((Ideal.absNorm I : ℝ)/Dstar)*W ((Ideal.absNorm I : ℝ)/D)

def plainCoefficient (χ : Character) (W : ℝ → ℂ) (N : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  IdealEuler.weighted (idealCoeff χ) s I*W ((Ideal.absNorm I : ℝ)/N)

lemma scaled_exp_log_product (x y D N R : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hD : 0 < D) (hN : 0 < N) :
    (D*N/R)*Real.exp (Real.log (x/D)+Real.log (y/N)) = x*y/R := by
  rw [Real.exp_add, Real.exp_log (div_pos hx hD), Real.exp_log (div_pos hy hN)]
  field_simp

theorem actual_pair_profile (χ : Character) (Ω V T W₁ W₂ : ℝ → ℂ)
    (Dstar D N Y U : ℝ) (hD : 0 < D) (hN : 0 < N) (s : ℂ)
    (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0)
    (hΩ : W₁ ((Ideal.absNorm I : ℝ)/D) ≠ 0 → W₂ ((Ideal.absNorm J : ℝ)/N) ≠ 0 →
      Ω (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) = 1) :
    HeckeDetectorPartition.pairCoefficient χ V T Dstar Y U s (I,J)*
      W₁ ((Ideal.absNorm I : ℝ)/D)*W₂ ((Ideal.absNorm J : ℝ)/N) =
      inverseCoefficient χ V W₁ Dstar D s I*plainCoefficient χ W₂ N s J*
        logSourceFun Ω V T (2*D*N/Dstar) (D*N/Y) (D*N/U)
          (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) := by
  by_cases hW₁ : W₁ ((Ideal.absNorm I : ℝ)/D) = 0
  · simp [hW₁, inverseCoefficient]
  by_cases hW₂ : W₂ ((Ideal.absNorm J : ℝ)/N) = 0
  · simp [hW₂, plainCoefficient]
  have hx : 0 < (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hy : 0 < (Ideal.absNorm J : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hscale (R : ℝ) := scaled_exp_log_product (Ideal.absNorm I) (Ideal.absNorm J) D N R hx hy hD hN
  have htwo : (2*D*N/Dstar)*Real.exp
      (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) =
        2*((Ideal.absNorm I : ℝ)*(Ideal.absNorm J : ℝ))/Dstar := by
    calc
      _ = 2*((D*N/Dstar)*Real.exp
        (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N))) := by ring
      _ = _ := by rw [hscale]; ring
  unfold HeckeDetectorPartition.pairCoefficient inverseCoefficient plainCoefficient logSourceFun
  rw [hΩ hW₁ hW₂, one_mul, htwo, hscale Y, hscale U, map_mul]
  simp only [map_mul, Nat.cast_mul, expNeg]
  push_cast
  ring_nf

theorem actual_finite_pair_separation (χ : Character) (Ω V T W₁ W₂ : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩs : ContDiff ℝ ∞ Ω)
    (hVs : ContDiff ℝ ∞ V) (hTs : ContDiff ℝ ∞ T)
    (Dstar D N Y U : ℝ) (hD : 0 < D) (hN : 0 < N) (s : ℂ)
    (S R : Finset (Ideal O)) (hS : ∀ I ∈ S, I ≠ 0) (hR : ∀ J ∈ R, J ≠ 0)
    (hΩ : ∀ I ∈ S, ∀ J ∈ R,
      W₁ ((Ideal.absNorm I : ℝ)/D) ≠ 0 → W₂ ((Ideal.absNorm J : ℝ)/N) ≠ 0 →
      Ω (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) = 1) :
    (∑ I ∈ S, ∑ J ∈ R, HeckeDetectorPartition.pairCoefficient χ V T Dstar Y U s (I,J)*
      W₁ ((Ideal.absNorm I : ℝ)/D)*W₂ ((Ideal.absNorm J : ℝ)/N)) =
      ∫ t : ℝ,
        (𝓕 (logSource Ω V T hΩc hΩs hVs hTs (2*D*N/Dstar) (D*N/Y) (D*N/U))) t*
        phasePolynomial S (inverseCoefficient χ V W₁ Dstar D s)
          (fun I => Real.log ((Ideal.absNorm I : ℝ)/D)) t*
        phasePolynomial R (plainCoefficient χ W₂ N s)
          (fun J => Real.log ((Ideal.absNorm J : ℝ)/N)) t := by
  rw [← finite_pair_separation]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  exact actual_pair_profile χ Ω V T W₁ W₂ Dstar D N Y U hD hN s I J
    (hS I hI) (hR J hJ) (hΩ I hI J hJ)

end
end SevenEighths.HeckeDetectorFourier

end OAI

end Source687

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorProfilesCutoffs.lean; sha256: 56f14a849cd2803d601da72ace45e533aa9f608c3ab8d5f16030eef0e32093a8 -/
section Source688
namespace OAI

namespace SevenEighths.HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

abbrev cutoff : SchwartzMap ℝ ℂ := QuadraticInitialBound.sieveCutoff

lemma cutoff_one (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) : cutoff x = 1 := by
  simp only [cutoff, QuadraticInitialBound.sieveCutoff_apply,
    QuadraticInitialBound.sieveBump_eq_one hx hx1, Complex.ofReal_one]

lemma cutoff_zero (x : ℝ) (hx : 2 ≤ x) : cutoff x = 0 := by
  rw [QuadraticInitialBound.sieveCutoff_apply]
  have hh := QuadraticInitialBound.sieveBump.zero_of_le_dist (x := x)
    (show QuadraticInitialBound.sieveBump.rOut ≤ dist x 0 by
      change 2 ≤ dist x 0
      simpa [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ x)] using hx)
  rw [hh, Complex.ofReal_zero]

lemma cutoff_norm_le (x : ℝ) : ‖cutoff x‖ ≤ 1 := by
  rw [QuadraticInitialBound.sieveCutoff_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg QuadraticInitialBound.sieveBump.nonneg]
  exact QuadraticInitialBound.sieveBump.le_one

lemma annular_log_bound (x : ℝ) (hx : 0 ≤ x)
    (hactive : DyadicTransfer.annularCutoff cutoff x ≠ 0) : |Real.log x| ≤ Real.log 2 := by
  have hh := HeckeDetectorPartition.annular_support cutoff cutoff_one cutoff_zero x hx 0
    (by simpa using hactive)
  norm_num at hh
  have hx0 : 0 < x := by linarith
  have hlo := Real.log_le_log (by norm_num : 0 < (2 : ℝ)⁻¹)
    (show (2 : ℝ)⁻¹ ≤ x by linarith)
  rw [Real.log_inv] at hlo
  exact abs_le.mpr ⟨hlo,Real.log_le_log hx0 hh.2.le⟩

theorem exists_product_log_cutoff :
    ∃ Ω : ℝ → ℂ, HasCompactSupport Ω ∧ ContDiff ℝ ∞ Ω ∧
      tsupport Ω ⊆ Set.Icc (-(2*Real.log 2+1)) (2*Real.log 2+1) ∧
      ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
        DyadicTransfer.annularCutoff cutoff x ≠ 0 → DyadicTransfer.annularCutoff cutoff y ≠ 0 →
        Ω (Real.log x+Real.log y) = 1 := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  obtain ⟨Ω,hc,hs,hone,hsupp,hzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff (2*Real.log 2) (by positivity)
  refine ⟨Ω,hc,hs,hsupp,?_⟩
  intro x y hx hy hax hay
  apply hone
  have hb1 := annular_log_bound x hx hax
  have hb2 := annular_log_bound y hy hay
  exact (abs_add_le _ _).trans (by linarith)

end
end SevenEighths.HeckeDetectorProfiles

end OAI

end Source688

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorTail.lean; sha256: ebf5f37d2824454f7434c661aa8f0ee2f05e6a2bbdcd5103f4c5ee32c3619c9d -/
section Source689
namespace OAI

noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorTail
open HeckeFamily HeckeDetectorWitnessArithmetic CompletedGauss
open IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

lemma exponential_cubic_bound (x Y : ℝ) (hx : 0 < x) (hY : 0 < Y) :
    x * Real.exp (-x/Y) ≤ 6*Y^3/x^2 := by
  have he := Real.pow_div_factorial_le_exp (x/Y) (show 0 ≤ x/Y by positivity) 3
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat] at he
  have hh := mul_le_mul_of_nonneg_right he (Real.exp_pos (-(x/Y))).le
  have hex : Real.exp (x/Y)*Real.exp (-(x/Y))=1 := by rw [←Real.exp_add]; simp
  rw [hex] at hh
  have hb : (x/Y)^3*Real.exp (-(x/Y)) ≤ 6 := by nlinarith
  calc
    _ = (Y^3/x^2)*((x/Y)^3*Real.exp (-(x/Y))) := by
      rw [neg_div]
      field_simp
    _ ≤ (Y^3/x^2)*6 := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

lemma divisor_count (I : Ideal O) (hI : I ≠ 0) :
    ((idealDivisors I).card : ℝ) ≤ 128*(Ideal.absNorm I : ℝ) := by
  apply DescentFiberCost.finite_ideal_count_real
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  · intro J hJ
    exact ne_zero_of_dvd_ne_zero hI ((mem_idealDivisors hI).mp hJ)
  · intro J hJ
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
      (map_dvd Ideal.absNorm ((mem_idealDivisors hI).mp hJ))

theorem cutoffCoefficient_bound (V : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (D : ℝ) (I : Ideal O) :
    ‖cutoffCoefficient V D I‖ ≤ 128*B*(Ideal.absNorm I : ℝ) := by
  by_cases hI : I = 0
  · simp [cutoffCoefficient,hI]
  rw [cutoffCoefficient,ite_eq_right hI]
  let e := mulFiberDivisorEquiv I hI
  have he : (∑' p : MulFiber I, (moebius p.val.1 : ℂ)*V ((Ideal.absNorm p.val.1 : ℝ)/D)) =
      ∑' J : {J : Ideal O // J ∈ idealDivisors I},
        (moebius J.val : ℂ)*V ((Ideal.absNorm J.val : ℝ)/D) :=
    e.tsum_eq (fun J => (moebius J.val : ℂ)*V ((Ideal.absNorm J.val : ℝ)/D))
  rw [he,tsum_fintype]
  calc
    _ ≤ ∑ J : {J : Ideal O // J ∈ idealDivisors I},
        ‖(moebius J.val : ℂ)*V ((Ideal.absNorm J.val : ℝ)/D)‖ := norm_sum_le _ _
    _ ≤ ∑ J : {J : Ideal O // J ∈ idealDivisors I}, B := by
      apply Finset.sum_le_sum
      intro J hJ
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (CubicEisenstein.norm_ideal_moebius_le_one _)).trans (hV _)
    _ = ((idealDivisors I).card : ℝ)*B := by simp
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right (divisor_count I hI) hB]

lemma norm_weight_two (I : Ideal O) (hI : I ≠ 0) :
    ‖CubicEisenstein.fullIdealWeight 2 I‖ = 1/(Ideal.absNorm I : ℝ)^2 := by
  rw [CubicEisenstein.fullIdealWeight,ite_eq_right hI,Complex.cpow_neg,Complex.cpow_ofNat,
    norm_inv,norm_pow,Complex.norm_natCast]
  simp [one_div]

lemma weighted_norm_le_one (χ : Character) (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖IdealEuler.weighted (idealCoeff χ) s I‖ ≤ 1 := by
  by_cases hI : I = 0
  · subst I
    rw [map_zero, norm_zero]
    norm_num
  have hN : 1 ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  change ‖idealCoeff χ I*CubicEisenstein.fullIdealWeight s I‖ ≤ 1
  rw [norm_mul,CubicEisenstein.fullIdealWeight,ite_eq_right hI]
  have hc : (Ideal.absNorm I : ℂ) = ((Ideal.absNorm I : ℝ) : ℂ) := by norm_cast
  rw [hc,Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ)<Ideal.absNorm I)]
  calc
    _ ≤ (1 : ℝ)*(Ideal.absNorm I : ℝ)^(-s.re) := by
      exact mul_le_mul_of_nonneg_right (idealCoeff_norm_le_one χ I) (by positivity)
    _ ≤ 1 := by
      simpa using Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr hs)

theorem exponentialTerm_bound (χ : Character) (V : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (D Y : ℝ) (hY : 0 < Y)
    (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖exponentialTerm χ V D s Y I‖ ≤
      (768*B*Y^3)*‖CubicEisenstein.fullIdealWeight 2 I‖ := by
  by_cases hI : I = 0
  · simp [hI,exponentialTerm,cutoffCoefficient,CubicEisenstein.fullIdealWeight]
  have hN : (0 : ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have he : ‖Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ)/(Y : ℂ))‖ =
      Real.exp (-(Ideal.absNorm I : ℝ)/Y) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  rw [exponentialTerm,norm_mul,norm_mul,he,norm_weight_two I hI]
  calc
    _ ≤ (128*B*(Ideal.absNorm I : ℝ))*Real.exp (-(Ideal.absNorm I : ℝ)/Y) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact (mul_le_mul (cutoffCoefficient_bound V B hB hV D I)
        (weighted_norm_le_one χ s hs I) (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
    _ ≤ (128*B)*(6*Y^3/(Ideal.absNorm I : ℝ)^2) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (exponential_cubic_bound _ Y hN hY) (by positivity)
    _ = _ := by ring

theorem exponentialTerm_summable (χ : Character) (V : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (D Y : ℝ) (hY : 0 < Y)
    (s : ℂ) (hs : 0 ≤ s.re) : Summable (exponentialTerm χ V D s Y) :=
  ((CubicEisenstein.fullIdealWeight_summable_norm 2 (by norm_num)).mul_left
    (768*B*Y^3)).of_norm_bounded (exponentialTerm_bound χ V B hB hV D Y hY s hs)

lemma cutoff_defect_bound (V : ℝ → ℂ) (B : ℝ)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (x : ℝ) : ‖1-V x‖ ≤ 1+B :=
  (norm_sub_le _ _).trans (by simpa using add_le_add_left (hV x) 1)

def terminalRemainder (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  exponentialTerm χ V D s Y I * (1-V (2*(Ideal.absNorm I : ℝ)/D)) *
    (1-T ((Ideal.absNorm I : ℝ)/U))

lemma exponentialTerm_half (χ : Character) (V : ℝ → ℂ) (D Y : ℝ)
    (_hY : 0 < Y) (s : ℂ) (I : Ideal O) :
    exponentialTerm χ V D s Y I = exponentialTerm χ V D s (2*Y) I *
      Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ)/(2*(Y : ℂ))) := by
  unfold exponentialTerm
  rw [mul_assoc (cutoffCoefficient V D I * IdealEuler.weighted (idealCoeff χ) s I),
    ←Complex.exp_add]
  congr 2
  push_cast
  ring

theorem terminalRemainder_bound (χ : Character) (V T : ℝ → ℂ) (B BT : ℝ)
    (hB : 0 ≤ B) (hBT : 0 ≤ BT)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (hT : ∀ x : ℝ, ‖T x‖ ≤ BT)
    (hTone : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1)
    (D Y U : ℝ) (hY : 0 < Y) (hU : 0 < U) (s : ℂ) (hs : 0 ≤ s.re)
    (I : Ideal O) :
    ‖terminalRemainder χ V T D Y U s I‖ ≤
      (6144*B*Y^3*(1+B)*(1+BT)*Real.exp (-U/(2*Y)))*
        ‖CubicEisenstein.fullIdealWeight 2 I‖ := by
  by_cases hI : (Ideal.absNorm I : ℝ) ≤ U
  · rw [terminalRemainder,hTone _ (by positivity) ((div_le_one hU).mpr hI)]
    simp only [sub_self,mul_zero,norm_zero]
    positivity
  have he : ‖Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ)/(2*(Y : ℂ)))‖ ≤
      Real.exp (-U/(2*Y)) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hc : (-((Ideal.absNorm I : ℝ) : ℂ)/(2*(Y : ℂ))).re =
        -(Ideal.absNorm I : ℝ)/(2*Y) := by
      rw [show (2 : ℂ)*(Y : ℂ) = ((2*Y : ℝ) : ℂ) by push_cast; rfl,
        ←Complex.ofReal_neg,←Complex.ofReal_div,Complex.ofReal_re]
    rw [hc]
    exact div_le_div_of_nonneg_right (by linarith [lt_of_not_ge hI]) (by positivity)
  rw [terminalRemainder,exponentialTerm_half χ V D Y hY s I]
  simp only [norm_mul]
  have h1 := mul_le_mul
    (exponentialTerm_bound χ V B hB hV D (2*Y) (by positivity) s hs I) he
    (norm_nonneg _) (by positivity)
  have h2 := mul_le_mul h1 (cutoff_defect_bound V B hV (2*(Ideal.absNorm I : ℝ)/D))
    (norm_nonneg _) (by positivity)
  have h3 := mul_le_mul h2 (cutoff_defect_bound T BT hT ((Ideal.absNorm I : ℝ)/U))
    (norm_nonneg _) (by positivity)
  apply h3.trans_eq
  ring

theorem terminalRemainder_summable (χ : Character) (V T : ℝ → ℂ) (B BT : ℝ)
    (hB : 0 ≤ B) (hBT : 0 ≤ BT)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (hT : ∀ x : ℝ, ‖T x‖ ≤ BT)
    (hTone : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1)
    (D Y U : ℝ) (hY : 0 < Y) (hU : 0 < U) (s : ℂ) (hs : 0 ≤ s.re) :
    Summable (terminalRemainder χ V T D Y U s) :=
  ((CubicEisenstein.fullIdealWeight_summable_norm 2 (by norm_num)).mul_left
    (6144*B*Y^3*(1+B)*(1+BT)*Real.exp (-U/(2*Y)))).of_norm_bounded
    (terminalRemainder_bound χ V T B BT hB hBT hV hT hTone D Y U hY hU s hs)

theorem terminalRemainder_tsum_bound (χ : Character) (V T : ℝ → ℂ) (B BT : ℝ)
    (hB : 0 ≤ B) (hBT : 0 ≤ BT)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (hT : ∀ x : ℝ, ‖T x‖ ≤ BT)
    (hTone : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1)
    (D Y U : ℝ) (hY : 0 < Y) (hU : 0 < U) (s : ℂ) (hs : 0 ≤ s.re) :
    ‖∑' I, terminalRemainder χ V T D Y U s I‖ ≤
      (6144*B*Y^3*(1+B)*(1+BT)*Real.exp (-U/(2*Y)))*
        ∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight 2 I‖ := by
  have hsum := terminalRemainder_summable χ V T B BT hB hBT hV hT hTone D Y U hY hU s hs
  apply (norm_tsum_le_tsum_norm hsum.norm).trans
  rw [←tsum_mul_left]
  exact hsum.norm.tsum_le_tsum
    (terminalRemainder_bound χ V T B BT hB hBT hV hT hTone D Y U hY hU s hs)
    ((CubicEisenstein.fullIdealWeight_summable_norm 2 (by norm_num)).mul_left _)

theorem terminalRemainder_uniform_small (B BT ε : ℝ)
    (hB : 0 ≤ B) (hBT : 0 ≤ BT) (hε : 0 < ε) :
    ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U → 1 ≤ U →
      ∀ (χ : Character) (V T : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ B) → (∀ x : ℝ, ‖T x‖ ≤ BT) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1) →
      ∀ (D : ℝ) (s : ℂ), 0 ≤ s.re →
      ‖∑' I, terminalRemainder χ V T D (U^20) (U^21) s I‖ < ε := by
  let C : ℝ := 6144*B*(1+B)*(1+BT)*(∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight 2 I‖)
  have ht : Tendsto (fun U : ℝ => C*(U^60*Real.exp (-U/2))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 60 (1/2) (by norm_num)).const_mul C
    convert h using 1
    · ext U
      rw [show (60 : ℝ) = ((60 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
      congr 2
      ring_nf
    · ring_nf
  obtain ⟨U₀,hU₀⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
  refine ⟨U₀,?_⟩
  intro U hU₀' hU χ V T hV hT hTone D s hs
  have hUpos : 0 < U := by linarith
  have hb := terminalRemainder_tsum_bound χ V T B BT hB hBT hV hT hTone
    D (U^20) (U^21) (by positivity) (by positivity) s hs
  have he : -(U^21)/(2*U^20) = -U/2 := by
    rw [show U^21 = U^20*U by ring]
    field_simp
  have hp : (U^20)^3 = U^60 := by ring
  rw [he,hp] at hb
  have hC : (6144*B*U^60*(1+B)*(1+BT)*Real.exp (-U/2))*
      (∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight 2 I‖) = C*(U^60*Real.exp (-U/2)) := by
    dsimp [C]
    ring
  rw [hC] at hb
  exact hb.trans_lt (hU₀ U hU₀')

theorem exponential_sum_tail_unconditional (χ : Character) (V : ℝ → ℂ)
    (B D Y : ℝ) (hB : 0 ≤ B) (hVbound : ∀ x : ℝ, ‖V x‖ ≤ B)
    (hD : 2 ≤ D) (hY : 0 < Y)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (hs : 0 ≤ s.re) :
    (∑' I : Ideal O, exponentialTerm χ V D s Y I * (1-V (2*(Ideal.absNorm I : ℝ)/D))) =
      (∑' I : Ideal O, exponentialTerm χ V D s Y I) - Complex.exp (-1/(Y : ℂ)) :=
  exponential_sum_tail χ V D hD hV hVzero s Y
    (exponentialTerm_summable χ V B hB hVbound D Y hY s hs)

def terminalTerm (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  exponentialTerm χ V D s Y I * (1-V (2*(Ideal.absNorm I : ℝ)/D)) *
    T ((Ideal.absNorm I : ℝ)/U)

private lemma summable_mul_bounded {A : Type*} (f g : A → ℂ)
    (hf : Summable f) (B : ℝ) (hg : ∀ a, ‖g a‖ ≤ B) :
    Summable (fun a => f a*g a) :=
  (hf.norm.mul_right B).of_norm_bounded (fun a => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hg a) (norm_nonneg _))

theorem terminal_sum_identity (χ : Character) (V T : ℝ → ℂ)
    (B BT D Y U : ℝ) (hB : 0 ≤ B)
    (hVbound : ∀ x : ℝ, ‖V x‖ ≤ B) (hTbound : ∀ x : ℝ, ‖T x‖ ≤ BT)
    (hD : 2 ≤ D) (hY : 0 < Y)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (hs : 0 ≤ s.re) :
    (∑' I : Ideal O, terminalTerm χ V T D Y U s I) =
      (∑' I : Ideal O, exponentialTerm χ V D s Y I) - Complex.exp (-1/(Y : ℂ)) -
        ∑' I : Ideal O, terminalRemainder χ V T D Y U s I := by
  let f := fun I : Ideal O => exponentialTerm χ V D s Y I * (1-V (2*(Ideal.absNorm I : ℝ)/D))
  have hf : Summable f := summable_mul_bounded _ _
    (exponentialTerm_summable χ V B hB hVbound D Y hY s hs) (1+B)
    (fun I => cutoff_defect_bound V B hVbound _)
  have hr : Summable (terminalRemainder χ V T D Y U s) :=
    summable_mul_bounded f _ hf (1+BT) (fun I => cutoff_defect_bound T BT hTbound _)
  have hi : terminalTerm χ V T D Y U s = fun I => f I-terminalRemainder χ V T D Y U s I := by
    funext I
    dsimp [f,terminalTerm,terminalRemainder]
    ring
  rw [hi,hf.tsum_sub hr]
  rw [show (∑' I, f I) = (∑' I, exponentialTerm χ V D s Y I)-Complex.exp (-1/(Y : ℂ)) from
    exponential_sum_tail_unconditional χ V B D Y hB hVbound hD hY hV hVzero s hs]

theorem terminal_sum_finite (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hTzero : ∀ x : ℝ, 2 ≤ x → T x = 0) (s : ℂ) :
    (∑' I : Ideal O, terminalTerm χ V T D Y U s I) =
      ∑ I ∈ ConcretePrimeRowBridge.idealsUpTo ⌈2*U⌉₊, terminalTerm χ V T D Y U s I := by
  apply tsum_eq_sum
  intro I hI
  by_cases hI0 : I = 0
  · simp [terminalTerm,exponentialTerm,cutoffCoefficient,hI0]
  have hN : (⌈2*U⌉₊ : ℝ) < Ideal.absNorm I := by
    have hn : ¬Ideal.absNorm I ≤ ⌈2*U⌉₊ := by
      intro hh
      apply hI
      exact ConcretePrimeRowBridge.mem_idealsUpTo.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI0),hh⟩
    exact_mod_cast lt_of_not_ge hn
  have ht : T ((Ideal.absNorm I : ℝ)/U)=0 := by
    apply hTzero
    apply (le_div_iff₀ hU).mpr
    linarith [Nat.le_ceil (2*U)]
  simp only [terminalTerm,ht,mul_zero]

end SevenEighths.HeckeDetectorTail

end

end OAI

end Source689

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorCoefficientBounds.lean; sha256: 6c782794201b4449e84a7c8be2b71baab283954a0b5a448bd0676f9011d3f4e3 -/
section Source690
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.HeckeDetectorCoefficientBounds
open HeckeFamily HeckeDetectorFourier HeckeDetectorTail
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma annular_norm_le_two (V : ℝ → ℂ) (hV : ∀ x, ‖V x‖ ≤ 1) (x : ℝ) :
    ‖DyadicTransfer.annularCutoff V x‖ ≤ 2 := by
  exact (norm_sub_le _ _).trans (by linarith [hV x,hV (2*x)])

lemma inverseCoefficient_norm_le_two (χ : Character) (V : ℝ → ℂ)
    (hV : ∀ x, ‖V x‖ ≤ 1) (Dstar D : ℝ) (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖inverseCoefficient χ V (DyadicTransfer.annularCutoff V) Dstar D s I‖ ≤ 2 := by
  simp only [inverseCoefficient,norm_mul]
  calc
    _ ≤ (1 : ℝ)*1*1*2 := by
      gcongr
      · exact CubicEisenstein.norm_ideal_moebius_le_one I
      · exact weighted_norm_le_one χ s hs I
      · exact hV _
      · exact annular_norm_le_two V hV _
    _ = _ := by norm_num

lemma plainCoefficient_norm_le_two (χ : Character) (V : ℝ → ℂ)
    (hV : ∀ x, ‖V x‖ ≤ 1) (N : ℝ) (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖plainCoefficient χ (DyadicTransfer.annularCutoff V) N s I‖ ≤ 2 := by
  simp only [plainCoefficient,norm_mul]
  calc
    _ ≤ (1 : ℝ)*2 := mul_le_mul (weighted_norm_le_one χ s hs I)
      (annular_norm_le_two V hV _) (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num

def expandedSet (U : ℝ) : Finset (Ideal O) := idealsUpTo ⌈16*U^21⌉₊

lemma expandedSet_count (U : ℝ) (hU : 1 ≤ U) :
    ((expandedSet U).card : ℝ) ≤ 4096*U^21 := by
  have hp : 1 ≤ U^21 := one_le_pow₀ hU
  have hc : (1 : ℝ) ≤ ⌈16*U^21⌉₊ := (by linarith : (1 : ℝ) ≤ 16*U^21).trans (Nat.le_ceil _)
  have h := DescentFiberCost.finite_ideal_count_real (expandedSet U) (⌈16*U^21⌉₊ : ℝ) hc
    (fun I hI => Ideal.absNorm_eq_zero_iff.not.mp (by have := (mem_idealsUpTo.mp hI).1; omega))
    (fun I hI => by exact_mod_cast (mem_idealsUpTo.mp hI).2)
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 16*U^21 by positivity)
  linarith

theorem coefficient_mass (χ : Character) (V : ℝ → ℂ) (hV : ∀ x, ‖V x‖ ≤ 1)
    (U Dstar D N : ℝ) (hU : 1 ≤ U) (s : ℂ) (hs : 0 ≤ s.re) :
    ((∑ I ∈ expandedSet U, ‖inverseCoefficient χ V (DyadicTransfer.annularCutoff V) Dstar D s I‖)*
      (∑ I ∈ expandedSet U, ‖plainCoefficient χ (DyadicTransfer.annularCutoff V) N s I‖)) ≤
      67108864*U^42 := by
  have hi : (∑ I ∈ expandedSet U,
      ‖inverseCoefficient χ V (DyadicTransfer.annularCutoff V) Dstar D s I‖) ≤ 8192*U^21 := by
    have h := Finset.sum_le_sum (s := expandedSet U)
      (fun I hI => inverseCoefficient_norm_le_two χ V hV Dstar D s hs I)
    simp only [Finset.sum_const, nsmul_eq_mul] at h
    linarith [expandedSet_count U hU]
  have hp : (∑ I ∈ expandedSet U,
      ‖plainCoefficient χ (DyadicTransfer.annularCutoff V) N s I‖) ≤ 8192*U^21 := by
    have h := Finset.sum_le_sum (s := expandedSet U)
      (fun I hI => plainCoefficient_norm_le_two χ V hV N s hs I)
    simp only [Finset.sum_const,nsmul_eq_mul] at h
    linarith [expandedSet_count U hU]
  have hh := mul_le_mul hi hp
    (Finset.sum_nonneg (fun I hI => norm_nonneg _)) (by positivity)
  apply hh.trans_eq
  ring

end SevenEighths.HeckeDetectorCoefficientBounds

end

end OAI

end Source690

/- Original source: OAI/NumberTheory/DirichletL/Hecke/Presentation.lean; sha256: 6d3ab5d6b1fe51409d259d966a4031d0257ba0c488e535660efcd08af6b15b47 -/
section Source691
namespace OAI

noncomputable section
open scoped Classical Topology
namespace SevenEighths.HeckePresentation
open HeckeFamily

def generator (η : Character) : O := ConcretePrimeRowBridge.idealGenerator η.modulus

instance (η : Character) : NeZero (generator η) :=
  ⟨ConcretePrimeRowBridge.idealGenerator_ne_zero η.modulus η.modulus_ne_bot⟩

theorem span_generator (η : Character) : Ideal.span {generator η} = η.modulus :=
  ConcretePrimeRowBridge.span_idealGenerator η.modulus

def quotientEquiv (η : Character) : (O ⧸ Ideal.span {generator η}) ≃+* (O ⧸ η.modulus) :=
  Ideal.quotEquivOfEq (span_generator η)

def principalResidue (η : Character) : MulChar (O ⧸ Ideal.span {generator η}) ℂ :=
  CharacterTransport.pullback (quotientEquiv η) η.residue

@[simp] theorem principalResidue_mk (η : Character) (z : O) :
    principalResidue η (Ideal.Quotient.mk (Ideal.span {generator η}) z) =
      elementCoeff η z := by
  simp only [principalResidue, CharacterTransport.pullback_apply, quotientEquiv,
    Ideal.quotEquivOfEq_mk, elementCoeff]

theorem principalResidue_unit (η : Character) (u : Oˣ) :
    principalResidue η (Ideal.Quotient.mk (Ideal.span {generator η}) (u : O)) = 1 := by
  rw [principalResidue_mk]
  exact η.unit_trivial u

def principalCharacter (η : Character) : Character :=
  HeckePrimitive.character (generator η) (principalResidue η) (principalResidue_unit η)

@[simp] theorem principalCharacter_elementCoeff (η : Character) (z : O) :
    elementCoeff (principalCharacter η) z = elementCoeff η z := principalResidue_mk η z

theorem principalResidue_primitive (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue) :
    FiniteFourier.IsPrimitiveOnIdeals (principalResidue η) :=
  CharacterTransport.primitive_pullback (quotientEquiv η) η.residue hp

private theorem pullback_one {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    CharacterTransport.pullback e (1 : MulChar S ℂ) = 1 := by
  apply MulChar.ext'
  intro x
  rw [CharacterTransport.pullback_apply]
  by_cases hx : IsUnit x
  · have hxe : IsUnit (e x) := hx.map e.toMonoidHom
    rw [MulChar.one_apply hxe, MulChar.one_apply hx]
  · have he : ¬ IsUnit (e x) := by
      intro h
      apply hx
      simpa using h.map e.symm.toMonoidHom
    rw [MulChar.map_nonunit _ he, MulChar.map_nonunit _ hx]

theorem principalResidue_ne_one (η : Character) (hη : η.residue ≠ 1) :
    principalResidue η ≠ 1 := by
  intro h
  have he := congrArg (CharacterTransport.pullback (quotientEquiv η).symm) h
  rw [principalResidue, CharacterTransport.pullback_symm, pullback_one] at he
  exact hη he

theorem LFunction_principalCharacter (η : Character) (hη : η.residue ≠ 1) (s : ℂ) :
    LFunction (principalCharacter η) s = LFunction η s := by
  have hp : (principalCharacter η).residue ≠ 1 := principalResidue_ne_one η hη
  have ha := LFunction_entire_nonprincipal (principalCharacter η) hp
  have hb := LFunction_entire_nonprincipal η hη
  have he : LFunction (principalCharacter η) = LFunction η := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr ha).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hb) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    unfold LFunction
    congr 1
    apply continuedLattice_eq_of_elementCoeff_eq _ _ (principalCharacter_elementCoeff η)
      (by linarith) (by intro h; norm_num [h] at hz)
  exact congr_fun he s

theorem uniform_strip_bound (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue) (hη : η.residue ≠ 1)
    (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖LFunction η z‖ ≤
      36 * ((1 + HeckeStrip.leftConstant) * HeckeReciprocalBound.bound (11/10)) *
        (η.modulus.absNorm : ℝ) ^ (3/5 : ℝ) * (3 + |z.im|)^2 := by
  have h := HeckeStripActual.uniform_strip_bound (generator η) (principalResidue η)
    (principalResidue_unit η) (principalResidue_primitive η hp) (principalResidue_ne_one η hη) z hz
  change ‖LFunction (principalCharacter η) z‖ ≤ _ at h
  rw [LFunction_principalCharacter η hη z] at h
  simpa only [HeckeStripActual.conductor, span_generator] using h

end SevenEighths.HeckePresentation

end

end OAI

end Source691

/- Original source: OAI/NumberTheory/DirichletL/LogarithmicControl.lean; sha256: d9d50528ba706c6b8704ebeb1b82232dd78bf382db3617e52fabf7ae17726bd1 -/
section Source692
namespace OAI

noncomputable section
open scoped Classical Topology
open Set Filter Metric Complex

namespace SevenEighths.LogarithmicControl

theorem differentiableOn_of_exp_eq {U : Set ℂ} (hU : IsOpen U)
    {L g : ℂ → ℂ} (hL : DifferentiableOn ℂ L U)
    (hg : ContinuousOn g U) (he : EqOn (Complex.exp ∘ g) L U) :
    DifferentiableOn ℂ g U := by
  intro z hz
  have hgc : ContinuousAt g z := (hg z hz).continuousAt (hU.mem_nhds hz)
  have hLc : DifferentiableAt ℂ L z := (hL z hz).differentiableAt (hU.mem_nhds hz)
  have hs := Complex.hasStrictDerivAt_exp (g z)
  let inv := hs.localInverse Complex.exp (Complex.exp (g z)) (g z)
    (Complex.exp_ne_zero _)
  have hi : DifferentiableAt ℂ inv (L z) := by
    rw [← he hz]
    exact (hs.to_localInverse (Complex.exp_ne_zero _)).hasDerivAt.differentiableAt
  have heq : (fun w ↦ inv (L w)) =ᶠ[𝓝 z] g := by
    have hlocal := hgc.eventually (hs.eventually_left_inverse (Complex.exp_ne_zero _))
    filter_upwards [hlocal, hU.mem_nhds hz] with w hw hwU
    simpa only [← he hwU, Function.comp_apply] using hw
  exact ((hi.comp z hLc).congr_of_eventuallyEq heq.symm).differentiableWithinAt

theorem exists_holomorphic_log {L : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball c R))
    (h0 : ∀ z ∈ ball c R, L z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧
      EqOn (Complex.exp ∘ g) L (ball c R) := by
  let : ContractibleSpace (ball c R) := contractibleSpace_ball hR
  have hsc : IsSimplyConnected (ball c R) := by
    change SimplyConnectedSpace (ball c R)
    infer_instance
  obtain ⟨g, hg, he⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc
    isOpen_ball hL.continuousOn (by
      rintro ⟨z, hz, heq⟩
      exact h0 z hz heq)
  exact ⟨g, differentiableOn_of_exp_eq isOpen_ball hL hg he, he⟩

theorem exists_holomorphic_log_normalized {L : ℂ → ℂ} {c m : ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball c R))
    (h0 : ∀ z ∈ ball c R, L z ≠ 0) (hm : Complex.exp m = L c) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧
      EqOn (Complex.exp ∘ g) L (ball c R) ∧ g c = m := by
  obtain ⟨g, hg, he⟩ := exists_holomorphic_log hR hL h0
  refine ⟨fun z ↦ g z + (m - g c), hg.add_const _, ?_, by simp⟩
  intro z hz
  change Complex.exp (g z + (m - g c)) = L z
  have hez : Complex.exp (g z) = L z := he hz
  have hec : Complex.exp (g c) = L c := he (mem_ball_self hR)
  rw [Complex.exp_add, Complex.exp_sub, hm, hez,
    hec, div_self (h0 c (mem_ball_self hR)), mul_one]

theorem log_eqOn_of_eq_center {g h : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball c r)) (hh : DifferentiableOn ℂ h (ball c r))
    (he : EqOn (Complex.exp ∘ g) (Complex.exp ∘ h) (ball c r)) (hc : g c = h c) :
    EqOn g h (ball c r) := by
  have hcm : c ∈ ball c r := mem_ball_self hr
  have hgc := (hg.continuousOn c hcm).continuousAt (isOpen_ball.mem_nhds hcm)
  have hhc := (hh.continuousOn c hcm).continuousAt (isOpen_ball.mem_nhds hcm)
  have hs := Complex.hasStrictDerivAt_exp (g c)
  have hleft := hs.eventually_left_inverse (Complex.exp_ne_zero _)
  have hgleft := hgc.eventually hleft
  have hhc' : Tendsto h (𝓝 c) (𝓝 (g c)) := by
    rw [hc]
    exact hhc.tendsto
  have hhleft := hhc'.eventually hleft
  have heq : g =ᶠ[𝓝 c] h := by
    filter_upwards [hgleft, hhleft, isOpen_ball.mem_nhds hcm] with z hz1 hz2 hz
    rw [← hz1, ← hz2]
    exact congrArg _ (he hz)
  exact (hg.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
    (hh.analyticOnNhd isOpen_ball) (convex_ball c r).isPreconnected hcm heq

theorem borel_caratheodory_closedBall {g : ℂ → ℂ} {c : ℂ} {r R M A : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hM : 0 < M) (hA : 0 ≤ A)
    (hg : DifferentiableOn ℂ g (ball c R))
    (hRe : ∀ z ∈ ball c R, (g z).re ≤ M) (hc : ‖g c‖ ≤ A)
    {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖g z‖ ≤ 2 * M * r / (R - r) + A * (R + r) / (R - r) := by
  have hzn : ‖z - c‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hz
  have hzR : ‖z - c‖ < R := hzn.trans_lt hrR
  have hRp : 0 < R := hr.trans_lt hrR
  have hg' : DifferentiableOn ℂ (fun w ↦ g (c + w)) (ball 0 R) := by
    apply hg.comp ((differentiable_const c).add differentiable_id).differentiableOn
    intro w hw
    simpa [mem_ball, dist_eq_norm] using hw
  have hb := Complex.borelCaratheodory hM hg' (fun w hw ↦ hRe _ (by
    simpa [mem_ball, dist_eq_norm] using hw)) (hr.trans_lt hrR)
    (show z - c ∈ ball 0 R by simpa using hzR)
  simp only [add_sub_cancel, add_zero] at hb
  refine hb.trans ?_
  apply add_le_add
  · gcongr
  · gcongr

theorem three_circles {g : ℂ → ℂ} {c z : ℂ} {r R S A B : ℝ}
    (hr : 0 < r) (hrR : r < R) (hRS : R < S)
    (hg : DifferentiableOn ℂ g (ball c S))
    (ha : ∀ w ∈ closedBall c r, ‖g w‖ ≤ A)
    (hb : ∀ w ∈ closedBall c R, ‖g w‖ ≤ B)
    (hzr : r ≤ ‖z - c‖) (hzR : ‖z - c‖ ≤ R) :
    ‖g z‖ ≤ A ^ (1 - (Real.log ‖z - c‖ - Real.log r) /
      (Real.log R - Real.log r)) *
      B ^ ((Real.log ‖z - c‖ - Real.log r) / (Real.log R - Real.log r)) := by
  let F : ℂ → ℂ := fun w ↦ g (c + Complex.exp w)
  have hRp : 0 < R := hr.trans hrR
  have hlog : Real.log r < Real.log R := Real.log_lt_log hr hrR
  have hmap (w : ℂ) (hw : w.re ≤ Real.log R) : c + Complex.exp w ∈ closedBall c R := by
    simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
    exact (Real.exp_le_exp.mpr hw).trans_eq (Real.exp_log hRp)
  have hclosed : closure (HadamardThreeLines.verticalStrip (Real.log r) (Real.log R)) ⊆
      HadamardThreeLines.verticalClosedStrip (Real.log r) (Real.log R) := by
    apply closure_minimal
    · intro w hw
      exact ⟨hw.1.le, hw.2.le⟩
    · exact isClosed_Icc.preimage Complex.continuous_re
  have hd : DiffContOnCl ℂ F
      (HadamardThreeLines.verticalStrip (Real.log r) (Real.log R)) := by
    apply DifferentiableOn.diffContOnCl
    intro w hw
    have hm := hmap w (hclosed hw).2
    have hm' : c + Complex.exp w ∈ ball c S :=
      closedBall_subset_ball hRS hm
    exact ((hg _ hm').differentiableAt (isOpen_ball.mem_nhds hm')).comp w
      ((differentiableAt_const c).add (Complex.differentiable_exp w)) |>.differentiableWithinAt
  have hbound : BddAbove ((norm ∘ F) ''
      HadamardThreeLines.verticalClosedStrip (Real.log r) (Real.log R)) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hb _ (hmap w hw.2)
  have hzn : 0 < ‖z - c‖ := hr.trans_le hzr
  have hz0 : z - c ≠ 0 := norm_pos_iff.mp hzn
  have hw : Complex.log (z - c) ∈
      HadamardThreeLines.verticalClosedStrip (Real.log r) (Real.log R) := by
    change Real.log r ≤ (Complex.log (z - c)).re ∧
      (Complex.log (z - c)).re ≤ Real.log R
    simp only [Complex.log_re]
    exact ⟨Real.log_le_log hr hzr, Real.log_le_log hzn hzR⟩
  have h := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    hlog hw hd hbound (a := A) (b := B) ?_ ?_
  · simpa [F, Complex.exp_log hz0, Complex.log_re] using h
  · intro w hw
    apply ha
    simp only [mem_preimage, mem_singleton_iff] at hw
    simp [mem_closedBall, dist_eq_norm, hw, Complex.norm_exp, Real.exp_log hr]
  · intro w hw
    exact hb _ (hmap w (le_of_eq hw))

theorem three_circles_power_bound {g : ℂ → ℂ} {c z : ℂ} {r ρ R S A B T : ℝ}
    (hr : 0 < r) (hrρ : r < ρ) (hρR : ρ < R) (hRS : R < S)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hT : 1 ≤ T)
    (hg : DifferentiableOn ℂ g (ball c S))
    (ha : ∀ w ∈ closedBall c r, ‖g w‖ ≤ A)
    (hb : ∀ w ∈ closedBall c R, ‖g w‖ ≤ B * T)
    (hz : z ∈ closedBall c ρ) :
    ‖g z‖ ≤ A * B * T ^ ((Real.log ρ - Real.log r) /
      (Real.log R - Real.log r)) := by
  let θ := (Real.log ρ - Real.log r) / (Real.log R - Real.log r)
  have hlogR : 0 < Real.log R - Real.log r :=
    sub_pos.mpr (Real.log_lt_log hr (hrρ.trans hρR))
  have hθ0 : 0 ≤ θ := div_nonneg
    (sub_nonneg.mpr (Real.log_le_log hr hrρ.le)) hlogR.le
  have hθ1 : θ ≤ 1 := (div_le_one hlogR).mpr (by
    linarith [Real.log_le_log (hr.trans hrρ) hρR.le])
  have hzn : ‖z - c‖ ≤ ρ := by simpa [mem_closedBall, dist_eq_norm] using hz
  have hAp : 0 ≤ A := zero_le_one.trans hA
  have hBp : 0 ≤ B := zero_le_one.trans hB
  have hTp : 0 ≤ T := zero_le_one.trans hT
  have hp1 : 1 ≤ T ^ θ := Real.one_le_rpow hT hθ0
  by_cases hzr : ‖z - c‖ ≤ r
  · have hgz := ha z (by simpa [mem_closedBall, dist_eq_norm] using hzr)
    exact hgz.trans (by nlinarith [mul_le_mul hB hp1 zero_le_one hBp])
  · have hzr' : r ≤ ‖z - c‖ := (lt_of_not_ge hzr).le
    have hzx : 0 < ‖z - c‖ := hr.trans_le hzr'
    let x := (Real.log ‖z - c‖ - Real.log r) / (Real.log R - Real.log r)
    have hx0 : 0 ≤ x := div_nonneg
      (sub_nonneg.mpr (Real.log_le_log hr hzr')) hlogR.le
    have hxθ : x ≤ θ := (div_le_div_iff_of_pos_right hlogR).mpr (by
      linarith [Real.log_le_log hzx hzn])
    have hx1 : x ≤ 1 := hxθ.trans hθ1
    have h := three_circles hr (hrρ.trans hρR) hRS hg ha hb hzr' (hzn.trans hρR.le)
    have hAa : A ^ (1 - x) ≤ A := by
      simpa using Real.rpow_le_rpow_of_exponent_le hA (show 1 - x ≤ 1 by linarith)
    have hBb : B ^ x ≤ B := by
      simpa using Real.rpow_le_rpow_of_exponent_le hB hx1
    have hTT : T ^ x ≤ T ^ θ := Real.rpow_le_rpow_of_exponent_le hT hxθ
    calc
      ‖g z‖ ≤ A ^ (1 - x) * (B * T) ^ x := h
      _ = A ^ (1 - x) * (B ^ x * T ^ x) := by rw [Real.mul_rpow hBp hTp]
      _ ≤ A * (B * T ^ θ) := mul_le_mul hAa
        (mul_le_mul hBb hTT (Real.rpow_nonneg hTp _) hBp)
        (by positivity) hAp
      _ = A * B * T ^ θ := by ring

def uniformTheta (e : ℝ) : ℝ := 1 - Real.log (1 + e) / Real.log (200 / 49)

theorem uniformTheta_mem {e : ℝ} (he : 0 < e) (he' : e < 1 / 1000) :
    0 < uniformTheta e ∧ uniformTheta e < 1 := by
  have hD : 0 < Real.log (200 / 49) := Real.log_pos (by norm_num)
  have hn : 0 < Real.log (1 + e) := Real.log_pos (by linarith)
  have hnD : Real.log (1 + e) < Real.log (200 / 49) :=
    Real.log_lt_log (by linarith) (by linarith)
  unfold uniformTheta
  constructor
  · linarith [(div_lt_one hD).mpr hnD]
  · linarith [div_pos hn hD]

theorem three_circles_exponent_uniform {a e : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000) :
    (Real.log (2 - a - 6 * e) - Real.log (49 / 100)) /
      (Real.log (2 - a - 4 * e) - Real.log (49 / 100)) ≤ uniformTheta e := by
  have hr : (0 : ℝ) < 49 / 100 := by norm_num
  have h6 : (49 / 100 : ℝ) < 2 - a - 6 * e := by linarith
  have h4 : (49 / 100 : ℝ) < 2 - a - 4 * e := by linarith
  have h6p : 0 < 2 - a - 6 * e := hr.trans h6
  have h4p : 0 < 2 - a - 4 * e := hr.trans h4
  have hep : 0 < 1 + e := by linarith
  have hD : 0 < Real.log (2 - a - 4 * e) - Real.log (49 / 100) :=
    sub_pos.mpr (Real.log_lt_log hr h4)
  have hU : 0 < Real.log (200 / 49) := Real.log_pos (by norm_num)
  have hDU : Real.log (2 - a - 4 * e) - Real.log (49 / 100) ≤
      Real.log (200 / 49) := by
    rw [← Real.log_div h4p.ne' hr.ne']
    apply Real.log_le_log (div_pos h4p hr)
    apply (div_le_iff₀ hr).mpr
    norm_num
    linarith
  have hprod : (2 - a - 6 * e) * (1 + e) ≤ 2 - a - 4 * e := by
    have : 2 - a - 6 * e ≤ 2 := by linarith
    nlinarith
  have hdiff : Real.log (1 + e) ≤ Real.log (2 - a - 4 * e) -
      Real.log (2 - a - 6 * e) := by
    have h := Real.log_le_log (mul_pos h6p hep) hprod
    rw [Real.log_mul h6p.ne' hep.ne'] at h
    linarith
  have hfrac : Real.log (1 + e) / Real.log (200 / 49) ≤
      (Real.log (2 - a - 4 * e) - Real.log (2 - a - 6 * e)) /
      (Real.log (2 - a - 4 * e) - Real.log (49 / 100)) := by
    gcongr
    exact (Real.log_pos (by linarith : 1 < 1 + e)).le.trans hdiff
  calc
    _ = 1 - (Real.log (2 - a - 4 * e) - Real.log (2 - a - 6 * e)) /
        (Real.log (2 - a - 4 * e) - Real.log (49 / 100)) := by
      apply eq_sub_iff_add_eq.mpr
      rw [← add_div]
      convert div_self hD.ne' using 1
      ring
    _ ≤ uniformTheta e := sub_le_sub_left hfrac 1

theorem exp_sublinear_le {θ K ε : ℝ} (hθ : 0 ≤ θ) (hθ' : θ < 1)
    (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, 1 ≤ x →
      Real.exp (K * x ^ θ) ≤ D * Real.exp (ε * x) := by
  have ht : Tendsto (fun x : ℝ ↦ K * x ^ (-(1 - θ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - θ)).const_mul K
  obtain ⟨X, hX⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  let Y := max 1 X
  refine ⟨Real.exp (K * Y ^ θ), Real.exp_pos _, ?_⟩
  intro x hx
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hYp : 0 < Y := zero_lt_one.trans_le (le_max_left _ _)
  by_cases hxy : x ≤ Y
  · have h1 : Real.exp (K * x ^ θ) ≤ Real.exp (K * Y ^ θ) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hxp.le hxy hθ) hK
    exact h1.trans (le_mul_of_one_le_right (Real.exp_pos _).le
      (Real.one_le_exp (by positivity)))
  · have hlarge := hX x ((le_max_right 1 X).trans (lt_of_not_ge hxy).le)
    have heq : K * x ^ θ = (K * x ^ (-(1 - θ))) * x := by
      have hp := Real.rpow_add hxp (-(1 - θ)) 1
      rw [Real.rpow_one] at hp
      rw [mul_assoc, ← hp]
      congr 2
      ring
    have hlin : K * x ^ θ ≤ ε * x := by
      rw [heq]
      exact mul_le_mul_of_nonneg_right hlarge.le hxp.le
    exact (Real.exp_le_exp.mpr hlin).trans (le_mul_of_one_le_left
      (Real.exp_pos _).le (Real.one_le_exp (mul_nonneg hK (Real.rpow_nonneg hYp.le _))))

def outerConstant (e A M : ℝ) : ℝ := (4 * M + 4 * A) / e

theorem outerConstant_ge_one {e A M : ℝ} (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) : 1 ≤ outerConstant e A M := by
  unfold outerConstant
  apply (le_div_iff₀ he).mpr
  nlinarith

theorem outer_log_bound {g : ℂ → ℂ} {c : ℂ} {a e A M T : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hg : DifferentiableOn ℂ g (ball c (2 - a - 2 * e)))
    (hRe : ∀ z ∈ ball c (2 - a - 3 * e), (g z).re ≤ M * T)
    (hc : ‖g c‖ ≤ A) {z : ℂ} (hz : z ∈ closedBall c (2 - a - 4 * e)) :
    ‖g z‖ ≤ outerConstant e A M * T := by
  have hAp : 0 ≤ A := zero_le_one.trans hA
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hb := borel_caratheodory_closedBall (by linarith : 0 ≤ 2 - a - 4 * e)
    (by linarith : 2 - a - 4 * e < 2 - a - 3 * e) (mul_pos hMp hTp) hAp
    (hg.mono (ball_subset_ball (by linarith))) hRe hc hz
  have hgap : 2 - a - 3 * e - (2 - a - 4 * e) = e := by ring
  rw [hgap] at hb
  have hfirst : 2 * (M * T) * (2 - a - 4 * e) ≤ 4 * M * T := by
    nlinarith [mul_le_mul_of_nonneg_left
      (show 2 - a - 4 * e ≤ 2 by linarith) (show 0 ≤ 2 * M * T by positivity)]
  have hsecond : A * (2 - a - 3 * e + (2 - a - 4 * e)) ≤ 4 * A * T := by
    have h1 := mul_le_mul_of_nonneg_left
      (show 2 - a - 3 * e + (2 - a - 4 * e) ≤ 4 by linarith) hAp
    nlinarith [mul_le_mul_of_nonneg_left hT (show 0 ≤ 4 * A by positivity)]
  refine hb.trans ?_
  rw [← add_div]
  unfold outerConstant
  rw [div_mul_eq_mul_div]
  exact (div_le_div_iff_of_pos_right he).mpr (by nlinarith)

theorem inner_log_bound {g : ℂ → ℂ} {c : ℂ} {a e A M T : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hg : DifferentiableOn ℂ g (ball c (2 - a - 2 * e)))
    (hRe : ∀ z ∈ ball c (2 - a - 3 * e), (g z).re ≤ M * T)
    (hin : ∀ z ∈ closedBall c (49 / 100), ‖g z‖ ≤ A)
    {z : ℂ} (hz : z ∈ closedBall c (2 - a - 6 * e)) :
    ‖g z‖ ≤ A * outerConstant e A M * T ^ uniformTheta e := by
  have hB := outerConstant_ge_one he he' hA hM
  have hb : ∀ w ∈ closedBall c (2 - a - 4 * e), ‖g w‖ ≤ outerConstant e A M * T :=
    fun w hw ↦ outer_log_bound ha ha' he he' hA hM hT hg hRe
      (hin c (mem_closedBall_self (by norm_num))) hw
  have h := three_circles_power_bound (by norm_num : (0 : ℝ) < 49 / 100)
    (by linarith : 49 / 100 < 2 - a - 6 * e)
    (by linarith : 2 - a - 6 * e < 2 - a - 4 * e)
    (by linarith : 2 - a - 4 * e < 2 - a - 2 * e)
    hA hB hT hg hin hb hz
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hT (three_circles_exponent_uniform ha ha' he he'))
    (by positivity))

theorem logarithm_derivative_bound {g : ℂ → ℂ} {c : ℂ} {a e A M T : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hg : DifferentiableOn ℂ g (ball c (2 - a - 2 * e)))
    (hRe : ∀ z ∈ ball c (2 - a - 3 * e), (g z).re ≤ M * T)
    (hc : ‖g c‖ ≤ A) {z : ℂ} (hz : z ∈ closedBall c (2 - a - 8 * e)) :
    ‖deriv g z‖ ≤ (outerConstant e A M / (2 * e)) * T := by
  have hzn : dist z c ≤ 2 - a - 8 * e := hz
  have hsub : closedBall z (2 * e) ⊆ ball c (2 - a - 2 * e) := by
    intro w hw
    have hw' : dist w z ≤ 2 * e := hw
    have hdist := dist_triangle w z c
    change dist w c < _
    linarith
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith : 0 < 2 * e)
    (hg.diffContOnCl_ball hsub) (C := outerConstant e A M * T) ?_
  · exact h.trans_eq (by ring)
  · intro w hw
    apply outer_log_bound ha ha' he he' hA hM hT hg hRe hc
    have hw' : dist w z = 2 * e := hw
    have hdist := dist_triangle w z c
    change dist w c ≤ _
    linarith

theorem zero_free_disk_logarithm {L E : ℂ → ℂ} {c : ℂ} {a e A M C : ℝ}
    (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000) (hC : 0 < C)
    (hL : DifferentiableOn ℂ L (ball c (2 - a - 2 * e)))
    (h0 : ∀ z ∈ ball c (2 - a - 2 * e), L z ≠ 0)
    (hpoly : ∀ z ∈ ball c (2 - a - 3 * e), ‖L z‖ ≤ C ^ M)
    (hE : DifferentiableOn ℂ E (ball c (1 / 2)))
    (hEL : EqOn (Complex.exp ∘ E) L (ball c (1 / 2)))
    (hEb : ∀ z ∈ closedBall c (49 / 100), ‖E z‖ ≤ A) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c (2 - a - 2 * e)) ∧
      EqOn (Complex.exp ∘ g) L (ball c (2 - a - 2 * e)) ∧
      (∀ z ∈ closedBall c (49 / 100), ‖g z‖ ≤ A) ∧
      (∀ z ∈ ball c (2 - a - 3 * e), (g z).re ≤ M * Real.log C) := by
  have hR : (1 / 2 : ℝ) < 2 - a - 2 * e := by linarith
  obtain ⟨g, hg, hge, hgc⟩ := exists_holomorphic_log_normalized
    (by linarith : 0 < 2 - a - 2 * e) hL h0
    (hEL (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)))
  have hgE : EqOn g E (ball c (1 / 2)) := log_eqOn_of_eq_center (by norm_num)
    (hg.mono (ball_subset_ball hR.le)) hE
    (fun z hz ↦ (hge (ball_subset_ball hR.le hz)).trans (hEL hz).symm) hgc
  refine ⟨g, hg, hge, ?_, ?_⟩
  · intro z hz
    rw [hgE (closedBall_subset_ball (by norm_num : (49 / 100 : ℝ) < 1 / 2) hz)]
    exact hEb z hz
  · intro z hz
    have hz' : z ∈ ball c (2 - a - 2 * e) := ball_subset_ball (by linarith) hz
    have hez : Complex.exp (g z) = L z := hge hz'
    have hp := hpoly z hz
    rw [← hez, Complex.norm_exp, Real.rpow_def_of_pos hC] at hp
    simpa [mul_comm] using Real.exp_le_exp.mp hp

theorem logarithmic_derivative_eq {L g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (he : EqOn (Complex.exp ∘ g) L U)
    {z : ℂ} (hz : z ∈ U) : deriv L z / L z = deriv g z := by
  have hgz := (hg z hz).differentiableAt (hU.mem_nhds hz)
  have hd := hgz.hasDerivAt.cexp
  have heq : L =ᶠ[𝓝 z] (fun w ↦ Complex.exp (g w)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (he hw).symm
  have hdl := hd.congr_of_eventuallyEq heq
  rw [hdl.deriv]
  have hez : Complex.exp (g z) = L z := he hz
  rw [← hez]
  field_simp

theorem logarithmic_control {e A M ε : ℝ}
    (he : 0 < e) (he' : e < 1 / 1000) (hA : 1 ≤ A) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (a C : ℝ) (L E : ℂ → ℂ) (c : ℂ),
      1 / 2 ≤ a → a ≤ 1 → Real.exp 1 ≤ C →
      DifferentiableOn ℂ L (ball c (2 - a - 2 * e)) →
      (∀ z ∈ ball c (2 - a - 2 * e), L z ≠ 0) →
      (∀ z ∈ ball c (2 - a - 3 * e), ‖L z‖ ≤ C ^ M) →
      DifferentiableOn ℂ E (ball c (1 / 2)) →
      EqOn (Complex.exp ∘ E) L (ball c (1 / 2)) →
      (∀ z ∈ closedBall c (49 / 100), ‖E z‖ ≤ A) →
      (∀ z ∈ closedBall c (2 - a - 6 * e), ‖L z‖ + ‖(L z)⁻¹‖ ≤ D * C ^ ε) ∧
      (∀ z ∈ closedBall c (2 - a - 8 * e),
        ‖deriv L z / L z‖ ≤ (outerConstant e A M / (2 * e)) * Real.log C) := by
  have hθ := uniformTheta_mem he he'
  have hB := outerConstant_ge_one he he' hA hM
  have hK : 0 ≤ A * outerConstant e A M := by positivity
  obtain ⟨D, hD, hDb⟩ := exp_sublinear_le hθ.1.le hθ.2 hK hε
  refine ⟨2 * D, by positivity, ?_⟩
  intro a C L E c ha ha' hC hL h0 hpoly hE hEL hEb
  have hCp : 0 < C := (Real.exp_pos 1).trans_le hC
  have hT : 1 ≤ Real.log C := by simpa using Real.log_le_log (Real.exp_pos 1) hC
  obtain ⟨g, hg, hge, hgin, hgRe⟩ :=
    zero_free_disk_logarithm ha' he he' hCp hL h0 hpoly hE hEL hEb
  constructor
  · intro z hz
    have hz' : z ∈ ball c (2 - a - 2 * e) :=
      closedBall_subset_ball (by linarith) hz
    have hez : Complex.exp (g z) = L z := hge hz'
    have hb := inner_log_bound ha ha' he he' hA hM hT hg hgRe hgin hz
    have hp : Real.exp (A * outerConstant e A M * Real.log C ^ uniformTheta e) ≤
        D * C ^ ε := by
      convert hDb (Real.log C) hT using 1
      rw [Real.rpow_def_of_pos hCp, mul_comm ε]
    have hu : ‖L z‖ ≤ D * C ^ ε := by
      rw [← hez, Complex.norm_exp]
      exact (Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hb)).trans hp
    have hl : ‖(L z)⁻¹‖ ≤ D * C ^ ε := by
      rw [← hez, ← Complex.exp_neg, Complex.norm_exp, Complex.neg_re]
      have hre : -(g z).re ≤ ‖g z‖ :=
        (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      exact (Real.exp_le_exp.mpr (hre.trans hb)).trans hp
    nlinarith
  · intro z hz
    rw [logarithmic_derivative_eq isOpen_ball hg hge
      (closedBall_subset_ball (by linarith) hz)]
    exact logarithm_derivative_bound ha ha' he he' hA hM hT hg hgRe
      (hgin c (mem_closedBall_self (by norm_num))) hz

theorem conductor_height_scale_ge_exp (Q t : ℝ) (hQ : 1 ≤ Q) :
    Real.exp 1 ≤ 2 * Q * (3 + |t|) ^ 2 := by
  have hs : 9 ≤ (3 + |t|) ^ 2 := by nlinarith [abs_nonneg t]
  have hq := mul_le_mul_of_nonneg_right hQ (sq_nonneg (3 + |t|))
  nlinarith [Real.exp_one_lt_three]

theorem absorb_polynomial_constant {K p : ℝ} (hp : 0 ≤ p) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ C : ℝ, Real.exp 1 ≤ C → K * C ^ p ≤ C ^ M := by
  let J := max 1 K
  have hJ : 1 ≤ J := le_max_left _ _
  have hJp : 0 < J := zero_lt_one.trans_le hJ
  have hlogJ : 0 ≤ Real.log J := Real.log_nonneg hJ
  refine ⟨p + Real.log J + 1, by linarith, ?_⟩
  intro C hC
  have hCp : 0 < C := (Real.exp_pos 1).trans_le hC
  have hlogC : 1 ≤ Real.log C := by simpa using Real.log_le_log (Real.exp_pos 1) hC
  have hJC : J ≤ C ^ Real.log J := by
    rw [Real.rpow_def_of_pos hCp, ← Real.exp_log hJp]
    simp only [Real.log_exp]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    K * C ^ p ≤ J * C ^ p := mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg hCp.le _)
    _ ≤ C ^ Real.log J * C ^ p := mul_le_mul_of_nonneg_right hJC
      (Real.rpow_nonneg hCp.le _)
    _ = C ^ (p + Real.log J) := by rw [← Real.rpow_add hCp]; congr 1; ring
    _ ≤ C ^ (p + Real.log J + 1) := Real.rpow_le_rpow_of_exponent_le
      ((show (1 : ℝ) ≤ Real.exp 1 by exact Real.one_le_exp (by norm_num)).trans hC)
      (by linarith)

theorem disk_re_gt {a e t : ℝ} {z : ℂ}
    (hz : z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - a - 2 * e)) :
    a + 2 * e < z.re := by
  have hn : ‖z - (2 + (t : ℂ) * Complex.I)‖ < 2 - a - 2 * e := by
    simpa [mem_ball, dist_eq_norm] using hz
  have hr := Complex.abs_re_le_norm (z - (2 + (t : ℂ) * Complex.I))
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
    Complex.I_im, zero_mul, sub_zero, add_zero] at hr
  norm_num at hr
  linarith [neg_le_abs (z.re - 2)]

theorem same_height_mem_disk {a e t v x : ℝ} (hev : 8 * e ≤ v)
    (hx : a + v ≤ x) (hx' : x ≤ 2) :
    (x : ℂ) + (t : ℂ) * Complex.I ∈
      closedBall (2 + (t : ℂ) * Complex.I) (2 - a - 8 * e) := by
  rw [mem_closedBall, dist_eq_norm]
  have heq : (x : ℂ) + (t : ℂ) * Complex.I - (2 + (t : ℂ) * Complex.I) =
      ((x - 2 : ℝ) : ℂ) := by push_cast; ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : x - 2 ≤ 0)]
  linarith

theorem principal_regularizer_norm_le_one {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(s - 1) / (s + 1)‖ ≤ 1 := by
  have hn : ‖s - 1‖ ≤ ‖s + 1‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im, sub_zero, Complex.add_re, Complex.add_im, add_zero]
    nlinarith
  rw [norm_div]
  exact div_le_one_of_le₀ hn (norm_nonneg _)

theorem principal_reciprocal_transfer {s Z L : ℂ} (hs : 0 ≤ s.re)
    (hL : L = ((s - 1) / (s + 1)) * Z) (h0 : L ≠ 0) : ‖Z⁻¹‖ ≤ ‖L⁻¹‖ := by
  have hf0 : (s - 1) / (s + 1) ≠ 0 := by
    intro hf
    apply h0
    rw [hL, hf, zero_mul]
  have heq : Z⁻¹ = ((s - 1) / (s + 1)) * L⁻¹ := by
    rw [hL, mul_inv]
    rw [← mul_assoc, mul_inv_cancel₀ hf0, one_mul]
  rw [heq, norm_mul]
  exact (mul_le_mul_of_nonneg_right (principal_regularizer_norm_le_one hs)
    (norm_nonneg _)).trans_eq (one_mul _)

end SevenEighths.LogarithmicControl

end

end OAI

end Source692

/- Original source: OAI/NumberTheory/DirichletL/Hecke/PrincipalStrip.lean; sha256: 4fe8823fa427f804e1b281e9bd7d8f5ab15183431db496f612d5c6a19f82454b -/
section Source693
namespace OAI

noncomputable section
open scoped Classical Topology
open Set MeasureTheory
namespace SevenEighths.HeckePrincipalStrip
open HeckeFamily HeckeTheta

def normalized (η : Character) (s : ℂ) : ℂ := HeckeOrigin.poleRemoved η s / (s+2)

theorem normalized_diffContOnCl (η : Character) :
    DiffContOnCl ℂ (normalized η) HeckeStrip.strip := by
  apply DifferentiableOn.diffContOnCl
  intro z hz
  exact ((HeckeOrigin.poleRemoved_entire η z).div (differentiableAt_id.add_const 2)
    (HeckeStrip.shift_ne_zero z (HeckeStrip.closure_strip_subset hz))).differentiableWithinAt

theorem norm_sub_one_le_shift (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖z-1‖ ≤ ‖z+2‖ := by
  have h : ‖z+2‖^2 - ‖z-1‖^2 = 6*z.re+3 := by
    norm_num [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im]
    ring
  nlinarith [hz.1, norm_nonneg (z-1), norm_nonneg (z+2)]

theorem normalized_norm_le (η : Character) {z : ℂ} (hz : z ∈ HeckeStrip.closedStrip)
    (h0 : z ≠ 0) (h1 : z ≠ 1) : ‖normalized η z‖ ≤ ‖LFunction η z‖ := by
  unfold normalized
  rw [HeckeOrigin.poleRemoved_eq η h0 h1, norm_div, norm_mul]
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (HeckeStrip.shift_norm_lower z hz))).mpr
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right (norm_sub_one_le_shift z hz)
    (norm_nonneg (LFunction η z))

private theorem norm_z_le_height (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖z‖ ≤ 3 + |z.im| := by
  apply (Complex.norm_le_abs_re_add_abs_im z).trans
  have hr : |z.re| ≤ 3 := abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
  linarith

private theorem norm_sub_one_le_height (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖z-1‖ ≤ 3 + |z.im| := by
  apply (Complex.norm_le_abs_re_add_abs_im (z-1)).trans
  have hr : |z.re-1| ≤ 3 := abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
  linarith

theorem regularized_completion_bound (η : Character) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ HeckeStrip.closedStrip,
      ‖HeckeMellinIdentity.regularized (pair (coefficients η)) z‖ ≤ C * (3+|z.im|)^2 := by
  let P := pair (coefficients η)
  have hstrong := P.isStrongFEPair_toStrongFEPair
  obtain ⟨C, hC, hbound⟩ := VerticalContourShift.mellin_uniform_strip_bound P.f_modif
    (-(1/10)) (11/10) (hstrong.hasMellin _).1 (hstrong.hasMellin _).1
  let D := C + ‖P.f₀‖ + ‖P.ε‖ * ‖P.g₀‖
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro z hz
  have hΛ : ‖P.Λ₀ z‖ ≤ C := hbound z hz.1 hz.2
  have hT : 1 ≤ 3+|z.im| := by linarith [abs_nonneg z.im]
  have hz0 := norm_z_le_height z hz
  have hz1 := norm_sub_one_le_height z hz
  unfold HeckeMellinIdentity.regularized
  change ‖z*(z-1)*P.Λ₀ z - (z-1)*P.f₀ + z*P.ε*P.g₀‖ ≤ _
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_sub_le _ _) (le_refl ‖z*P.ε*P.g₀‖)).trans
  simp only [norm_mul]
  calc
    _ ≤ ((3+|z.im|)*(3+|z.im|))*C + (3+|z.im|)*‖P.f₀‖ +
        (3+|z.im|)*‖P.ε‖*‖P.g₀‖ := by gcongr
    _ ≤ D*(3+|z.im|)^2 := by
      dsimp [D]
      have hf := norm_nonneg P.f₀
      have hg := mul_nonneg (norm_nonneg P.ε) (norm_nonneg P.g₀)
      have hsq : 3+|z.im| ≤ (3+|z.im|)^2 := by nlinarith
      nlinarith

theorem normalized_exp_growth (η : Character) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z ∈ HeckeStrip.strip,
      ‖normalized η z‖ ≤ A * Real.exp (B * |z.im|) := by
  obtain ⟨C, hC, hCbound⟩ := regularized_completion_bound η
  obtain ⟨G, hG, hGbound⟩ := CubicGammaExponential.inverse_Gamma_strip_exp_bound_complex
    (9/10) (21/10)
  let S : ℝ := Real.pi ^ (-(1/10) : ℝ) + Real.pi ^ (11/10 : ℝ)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  refine ⟨9*S*G*C, Real.pi+2, by positivity, by positivity, ?_⟩
  intro z hz
  have hzc : z ∈ HeckeStrip.closedStrip := ⟨hz.1.le, hz.2.le⟩
  have hp : ‖(Real.pi : ℂ)^z‖ ≤ S := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    exact VerticalContourShift.rpow_between_endpoints Real.pi (-(1/10)) (11/10) z.re
      Real.pi_pos hzc.1 hzc.2
  have hg : ‖(Complex.Gamma (z+1))⁻¹‖ ≤ G*Real.exp (Real.pi*|z.im|) := by
    simpa using hGbound (z+1) (by constructor <;> simp only [Complex.add_re, Complex.one_re] <;>
      linarith [hzc.1, hzc.2])
  have ht : (3+|z.im|)^2 ≤ 9*Real.exp (2*|z.im|) := by
    have he := Real.add_one_le_exp |z.im|
    have ht0 := abs_nonneg z.im
    have hle : 3+|z.im| ≤ 3*Real.exp |z.im| := by linarith
    have hs := sq_le_sq₀ (by positivity : 0 ≤ 3+|z.im|) (by positivity : 0 ≤ 3*Real.exp |z.im|)
    have hsq := hs.mpr hle
    rw [mul_pow, ← Real.exp_nat_mul] at hsq
    norm_num at hsq ⊢
    exact hsq
  unfold normalized HeckeOrigin.poleRemoved
  simp only [norm_div, norm_mul]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ ‖(Real.pi : ℂ)^z‖ * ‖(Complex.Gamma (z+1))⁻¹‖ *
        ‖HeckeMellinIdentity.regularized (pair (coefficients η)) z‖ := by
      apply (div_le_self (by positivity) (HeckeStrip.shift_norm_lower z hzc)).trans
      exact div_le_self (by positivity) (by norm_num)
    _ ≤ S * (G*Real.exp (Real.pi*|z.im|)) * (C*(3+|z.im|)^2) := by
      gcongr
      exact hCbound z hzc
    _ ≤ S * (G*Real.exp (Real.pi*|z.im|)) * (C*(9*Real.exp (2*|z.im|))) := by gcongr
    _ = _ := by
      rw [show (Real.pi+2)*|z.im| = Real.pi*|z.im| + 2*|z.im| by ring, Real.exp_add]
      ring

theorem primitive_normalized_bound (c : O) [NeZero c]
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ)
    (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖normalized (HeckePrimitive.character c χ hu) z‖ ≤
      36 * ((1+HeckeStrip.leftConstant)*HeckeReciprocalBound.bound (11/10)) *
        HeckeStripActual.conductor c ^ (3/5 : ℝ) * (3+|z.im|)^2 := by
  let η := HeckePrimitive.character c χ hu
  let D := HeckeReciprocalBound.bound (11/10)
  have hD : 0 ≤ D := tsum_nonneg (fun _ => norm_nonneg _)
  have hc := HeckeStrip.leftConstant_pos
  have hQ := HeckeStripActual.conductor_ge_one c
  apply HeckeStrip.uniform_strip_bound (HeckeStripActual.conductor c)
    ((1+HeckeStrip.leftConstant)*D) hQ (by positivity) (normalized η)
    (normalized_diffContOnCl η) (normalized_exp_growth η) ?_ ?_ z hz
  · intro w hw
    have hwc : w ∈ HeckeStrip.closedStrip := ⟨by rw [hw], by rw [hw]; norm_num⟩
    apply (normalized_norm_le η hwc (by intro h; simp [h] at hw)
      (by intro h; norm_num [h] at hw)).trans
    have hb := HeckeStrip.left_boundary_of_functional_equation
      (HeckeStripActual.conductor c) D (lt_of_lt_of_le zero_lt_one hQ) hD
      (LFunction η) (LFunction (HeckePrimitive.character c χ⁻¹
        (HeckePrimitive.inverse_unit_trivial c χ hu))) (TraceCharacter.normalizedGauss c χ)
      (TraceCharacter.normalizedGauss_norm c χ hp)
      (fun _ hs => HeckeStripActual.functional_equation_left c χ hu hp hs)
      (fun _ hs => HeckeStripActual.LFunction_norm_le _ (by norm_num : (1 : ℝ)<11/10) hs.ge) w hw
    apply hb.trans
    have hbase : HeckeStrip.leftConstant*D ≤ (1+HeckeStrip.leftConstant)*D := by nlinarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg (by linarith) _)) (sq_nonneg _)
  · intro w hw
    have hwc : w ∈ HeckeStrip.closedStrip := ⟨by rw [hw]; norm_num, by rw [hw]⟩
    apply (normalized_norm_le η hwc (by intro h; norm_num [h] at hw)
      (by intro h; norm_num [h] at hw)).trans
    apply (HeckeStripActual.LFunction_norm_le η (by norm_num : (1 : ℝ)<11/10) hw.ge).trans
    change D ≤ (1+HeckeStrip.leftConstant)*D
    nlinarith

theorem poleRemoved_principalCharacter (η : Character) (s : ℂ) :
    HeckeOrigin.poleRemoved (HeckePresentation.principalCharacter η) s =
      HeckeOrigin.poleRemoved η s := by
  have he : HeckeOrigin.poleRemoved (HeckePresentation.principalCharacter η) =
      HeckeOrigin.poleRemoved η := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (HeckeOrigin.poleRemoved_entire _)).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (HeckeOrigin.poleRemoved_entire _)) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds
      (by norm_num : (1 : ℝ)<(2 : ℂ).re)] with z hz
    have h0 : z ≠ 0 := by intro h; norm_num [h] at hz
    have h1 : z ≠ 1 := by intro h; norm_num [h] at hz
    rw [HeckeOrigin.poleRemoved_eq _ h0 h1, HeckeOrigin.poleRemoved_eq _ h0 h1]
    congr 1
    unfold LFunction
    congr 1
    exact continuedLattice_eq_of_elementCoeff_eq _ _
      (HeckePresentation.principalCharacter_elementCoeff η) (by linarith) h1
  exact congr_fun he s

theorem uniform_normalized_strip_bound (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue)
    (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖normalized η z‖ ≤
      36 * ((1+HeckeStrip.leftConstant)*HeckeReciprocalBound.bound (11/10)) *
        (η.modulus.absNorm : ℝ) ^ (3/5 : ℝ) * (3+|z.im|)^2 := by
  have h := primitive_normalized_bound (HeckePresentation.generator η)
    (HeckePresentation.principalResidue η) (HeckePresentation.principalResidue_unit η)
    (HeckePresentation.principalResidue_primitive η hp) z hz
  change ‖normalized (HeckePresentation.principalCharacter η) z‖ ≤ _ at h
  unfold normalized at h ⊢
  rw [poleRemoved_principalCharacter] at h
  simpa only [HeckeStripActual.conductor, HeckePresentation.span_generator] using h

def sourceNormalized (η : Character) (s : ℂ) : ℂ :=
  HeckeOrigin.poleRemoved η s / (s+1)

theorem sourceNormalized_norm_le (η : Character) (z : ℂ)
    (hz : z ∈ HeckeStrip.closedStrip) :
    ‖sourceNormalized η z‖ ≤ 3 * ‖normalized η z‖ := by
  have hlow : (9/10 : ℝ) ≤ ‖z+1‖ := by
    have hre := Complex.re_le_norm (z+1)
    simp only [Complex.add_re, Complex.one_re] at hre
    linarith [hz.1]
  have hn1 : z+1 ≠ 0 := norm_pos_iff.mp (by linarith)
  have hn2 : z+2 ≠ 0 := HeckeStrip.shift_ne_zero z hz
  have hratio : ‖z+2‖ ≤ 3*‖z+1‖ := by
    have ht := norm_add_le (z+1) (1 : ℂ)
    rw [norm_one, show z+1+1=z+2 by ring] at ht
    linarith
  have heq : sourceNormalized η z = normalized η z * ((z+2)/(z+1)) := by
    unfold sourceNormalized normalized
    field_simp
  rw [heq, norm_mul, norm_div]
  have hd : ‖z+2‖ / ‖z+1‖ ≤ 3 := (div_le_iff₀ (norm_pos_iff.mpr hn1)).mpr hratio
  nlinarith [norm_nonneg (normalized η z)]

theorem uniform_source_normalized_strip_bound (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue)
    (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖sourceNormalized η z‖ ≤
      108 * ((1+HeckeStrip.leftConstant)*HeckeReciprocalBound.bound (11/10)) *
        (η.modulus.absNorm : ℝ) ^ (3/5 : ℝ) * (3+|z.im|)^2 := by
  apply (sourceNormalized_norm_le η z hz).trans
  have h := mul_le_mul_of_nonneg_left (uniform_normalized_strip_bound η hp z hz) (by norm_num : (0 : ℝ) ≤ 3)
  convert h using 1 ; ring

end SevenEighths.HeckePrincipalStrip

end

end OAI

end Source693

/- Original source: OAI/NumberTheory/DirichletL/Hecke/LogarithmicInput.lean; sha256: e210ffe3239034cc9011145ced17576d67ae0c77cd00855add998311a3efcf7d -/
section Source694
namespace OAI

noncomputable section
open scoped Classical Topology
open Set
namespace SevenEighths.HeckeLogarithmicInput
open HeckeFamily

def regular (η : Character) (s : ℂ) : ℂ :=
  if η.residue = 1 then HeckePrincipalStrip.sourceNormalized η s else LFunction η s

theorem regular_eq_nonprincipal (η : Character) (hη : η.residue ≠ 1) :
    regular η = LFunction η := by funext s; simp [regular, hη]

theorem regular_differentiableAt (η : Character) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (regular η) s := by
  have hplus : s+1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
    linarith
  by_cases hη : η.residue = 1
  · have he : regular η = HeckePrincipalStrip.sourceNormalized η := by
      funext z; simp [regular, hη]
    rw [he]
    exact (HeckeOrigin.poleRemoved_entire η s).div (differentiableAt_id.add_const 1) hplus
  · rw [regular_eq_nonprincipal η hη]
    exact LFunction_entire_nonprincipal η hη s

theorem regular_ne_zero (η : Character) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) : regular η s ≠ 0 := by
  have hs0 : 0 < s.re := by linarith [HeckeZeroSupremum.half_le_beta]
  have h0 : s ≠ 0 := by intro h; simp [h] at hs0
  have hplus : s+1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
    linarith
  by_cases hη : η.residue = 1
  · simp only [regular, ite_eq_left hη, HeckePrincipalStrip.sourceNormalized]
    apply div_ne_zero _ hplus
    by_cases h1 : s = 1
    · subst s; exact HeckeOrigin.poleRemoved_one_ne_zero η hη
    · rw [HeckeOrigin.poleRemoved_eq η h0 h1]
      exact mul_ne_zero (sub_ne_zero.mpr h1)
        (HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt η hs (Or.inl h1))
  · rw [regular_eq_nonprincipal η hη]
    exact HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt η hs (Or.inr hη)

theorem regular_inverse_differentiableAt (η : Character) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) :
    DifferentiableAt ℂ (fun z => (regular η z)⁻¹) s :=
  (regular_differentiableAt η (by linarith [HeckeZeroSupremum.half_le_beta])).inv
    (regular_ne_zero η hs)

theorem principal_regular_factor_bound {s : ℂ} (hs : 0 ≤ s.re) :
    ‖s-1‖ ≤ ‖s+1‖ := by
  have he : ‖s+1‖^2 - ‖s-1‖^2 = 4*s.re := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  nlinarith [norm_nonneg (s-1), norm_nonneg (s+1)]

theorem regular_norm_le (η : Character) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) : ‖regular η s‖ ≤ HeckeReciprocalBound.bound σ := by
  by_cases hη : η.residue = 1
  · have h0 : s ≠ 0 := by intro h; simp [h] at hs; linarith
    have h1 : s ≠ 1 := by intro h; simp [h] at hs; linarith
    have hp : 0 < ‖s+1‖ := by
      have hr := Complex.re_le_norm (s+1)
      simp only [Complex.add_re, Complex.one_re] at hr
      linarith
    simp only [regular, ite_eq_left hη, HeckePrincipalStrip.sourceNormalized,
      HeckeOrigin.poleRemoved_eq η h0 h1, norm_div, norm_mul]
    apply le_trans _ (HeckeStripActual.LFunction_norm_le η hσ hs)
    apply (div_le_iff₀ hp).mpr
    nlinarith [principal_regular_factor_bound (s := s) (by linarith), norm_nonneg (LFunction η s)]
  · rw [regular_eq_nonprincipal η hη]
    exact HeckeStripActual.LFunction_norm_le η hσ hs

theorem regular_inverse_norm_le (η : Character) {s : ℂ} (hs : (3/2 : ℝ) ≤ s.re) :
    ‖(regular η s)⁻¹‖ ≤ 5 * HeckeReciprocalBound.bound (3/2) := by
  have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
  have hL := HeckeReciprocalBound.reciprocal_norm_le η (by norm_num : (1 : ℝ)<3/2) hs
  rw [HeckeReciprocal.reciprocal_eq_inv η h0 h1] at hL
  have hB : 0 ≤ HeckeReciprocalBound.bound (3/2) := tsum_nonneg (fun _ => norm_nonneg _)
  by_cases hη : η.residue = 1
  · have hlow : (1/2 : ℝ) ≤ ‖s-1‖ := by
      have hr := Complex.re_le_norm (s-1)
      simp only [Complex.sub_re, Complex.one_re] at hr
      linarith
    have hratio : ‖s+1‖ / ‖s-1‖ ≤ 5 := by
      apply (div_le_iff₀ (by linarith : 0 < ‖s-1‖)).mpr
      have hr := norm_add_le (s-1) (2 : ℂ)
      norm_num only [Complex.norm_ofNat] at hr
      rw [show s-1+2=s+1 by ring] at hr
      linarith
    simp only [regular, ite_eq_left hη, HeckePrincipalStrip.sourceNormalized,
      HeckeOrigin.poleRemoved_eq η h0 h1, inv_div, norm_div, norm_mul]
    calc
      _ = (‖s+1‖ / ‖s-1‖) * ‖(LFunction η s)⁻¹‖ := by rw [norm_inv]; ring
      _ ≤ _ := mul_le_mul hratio hL (norm_nonneg _) (by norm_num)
  · rw [regular_eq_nonprincipal η hη]
    linarith

def uniformConstant : ℝ :=
  108*((1+HeckeStrip.leftConstant)*HeckeReciprocalBound.bound (11/10))

theorem uniformConstant_nonneg : 0 ≤ uniformConstant := by
  have hc := HeckeStrip.leftConstant_pos
  have hD : 0 ≤ HeckeReciprocalBound.bound (11/10) := tsum_nonneg (fun _ => norm_nonneg _)
  unfold uniformConstant
  positivity

theorem modulus_norm_ge_one (η : Character) : 1 ≤ (η.modulus.absNorm : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)

theorem regular_strip_bound (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue) (z : ℂ)
    (hz : z ∈ HeckeStrip.closedStrip) :
    ‖regular η z‖ ≤ uniformConstant * (η.modulus.absNorm : ℝ)^(3/5 : ℝ) *
      (3+|z.im|)^2 := by
  by_cases hη : η.residue = 1
  · simpa only [regular, ite_eq_left hη, uniformConstant] using
      HeckePrincipalStrip.uniform_source_normalized_strip_bound η hp z hz
  · rw [regular_eq_nonprincipal η hη]
    apply (HeckePresentation.uniform_strip_bound η hp hη z hz).trans
    have hc := HeckeStrip.leftConstant_pos
    have hD : 0 ≤ HeckeReciprocalBound.bound (11/10) := tsum_nonneg (fun _ => norm_nonneg _)
    unfold uniformConstant
    gcongr ; norm_num

theorem regular_right_growth (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue) {z : ℂ}
    (hz : -(1/10 : ℝ) ≤ z.re) :
    ‖regular η z‖ ≤ uniformConstant * (η.modulus.absNorm : ℝ)^(3/5 : ℝ) *
      (3+|z.im|)^2 := by
  by_cases hright : z.re ≤ 11/10
  · exact regular_strip_bound η hp z ⟨hz, hright⟩
  · apply (regular_norm_le η (by norm_num : (1 : ℝ)<11/10) (le_of_not_ge hright)).trans
    have hD : 0 ≤ HeckeReciprocalBound.bound (11/10) := tsum_nonneg (fun _ => norm_nonneg _)
    have hc := HeckeStrip.leftConstant_pos
    have hC : HeckeReciprocalBound.bound (11/10) ≤ uniformConstant := by
      unfold uniformConstant; nlinarith
    have hQ : 1 ≤ (η.modulus.absNorm : ℝ)^(3/5 : ℝ) :=
      Real.one_le_rpow (modulus_norm_ge_one η) (by norm_num)
    have hT : 1 ≤ (3+|z.im|)^2 := by nlinarith [abs_nonneg z.im]
    exact hC.trans ((le_mul_of_one_le_right uniformConstant_nonneg hQ).trans
      (le_mul_of_one_le_right (mul_nonneg uniformConstant_nonneg (by linarith : 0 ≤ (η.modulus.absNorm : ℝ)^(3/5 : ℝ))) hT))

theorem regular_ne_zero_on_disk (η : Character) (a e t : ℝ)
    (ha : HeckeZeroSupremum.beta ≤ a) (he : 0 < e) {z : ℂ}
    (hz : z ∈ Metric.ball ((2 : ℂ)+t*Complex.I) (2-a-2*e)) :
    regular η z ≠ 0 := by
  apply regular_ne_zero η
  have hn : ‖z-((2 : ℂ)+t*Complex.I)‖ < 2-a-2*e := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hr := Complex.abs_re_le_norm (z-((2 : ℂ)+t*Complex.I))
  have hrl := neg_abs_le (z-((2 : ℂ)+t*Complex.I)).re
  norm_num [Complex.sub_re, Complex.add_re, Complex.mul_re] at hr hrl
  linarith

theorem reciprocal_norm_le_regular_inverse (η : Character) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) :
    ‖HeckeReciprocal.reciprocal η s‖ ≤ ‖(regular η s)⁻¹‖ := by
  have hs0 : 0 < s.re := by linarith [HeckeZeroSupremum.half_le_beta]
  have h0 : s ≠ 0 := by intro h; simp [h] at hs0
  by_cases hη : η.residue = 1
  · by_cases h1 : s = 1
    · subst s
      rw [HeckeReciprocal.reciprocal_principal_one η hη, norm_zero]
      exact norm_nonneg _
    have hp : s+1 ≠ 0 := by
      intro h
      have he := congrArg Complex.re h
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
      linarith
    have hL := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt η hs (Or.inl h1)
    have he : HeckeReciprocal.reciprocal η s =
        ((s-1)/(s+1))*(regular η s)⁻¹ := by
      rw [HeckeReciprocal.reciprocal_eq_inv η h0 h1]
      simp only [regular, ite_eq_left hη, HeckePrincipalStrip.sourceNormalized,
        HeckeOrigin.poleRemoved_eq η h0 h1]
      field_simp
    rw [he, norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr hp)).mpr (principal_regular_factor_bound hs0.le)
  · simp only [HeckeReciprocal.reciprocal, regular, ite_eq_right hη, le_refl]

theorem regular_disk_growth (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue) (a e t : ℝ)
    (ha : (1/2 : ℝ) ≤ a) (he : 0 ≤ e) {z : ℂ}
    (hz : z ∈ Metric.closedBall ((2 : ℂ)+t*Complex.I) (2-a-2*e)) :
    ‖regular η z‖ ≤ (4*uniformConstant) * (η.modulus.absNorm : ℝ)^(3/5 : ℝ) *
      (3+|t|)^2 := by
  have hn : ‖z-((2 : ℂ)+t*Complex.I)‖ ≤ 2-a-2*e := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hr := Complex.abs_re_le_norm (z-((2 : ℂ)+t*Complex.I))
  have hi := Complex.abs_im_le_norm (z-((2 : ℂ)+t*Complex.I))
  norm_num [Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.sub_im, Complex.add_im, Complex.mul_im] at hr hi
  have hzre : -(1/10 : ℝ) ≤ z.re := by
    have hh := neg_abs_le (z.re-2)
    linarith
  have hheight : 3+|z.im| ≤ 2*(3+|t|) := by
    have hab := abs_add_le (z.im-t) t
    rw [sub_add_cancel] at hab
    linarith [abs_nonneg t]
  apply (regular_right_growth η hp hzre).trans
  have hsq : (3+|z.im|)^2 ≤ 4*(3+|t|)^2 := by
    have h := (sq_le_sq₀ (by positivity : 0 ≤ 3+|z.im|)
      (by positivity : 0 ≤ 2*(3+|t|))).mpr hheight
    nlinarith
  calc
    _ ≤ uniformConstant*(η.modulus.absNorm : ℝ)^(3/5 : ℝ)*(4*(3+|t|)^2) :=
      mul_le_mul_of_nonneg_left hsq (mul_nonneg uniformConstant_nonneg (Real.rpow_nonneg (by positivity) _))
    _ = _ := by ring

end SevenEighths.HeckeLogarithmicInput

end

end OAI

end Source694

/- Original source: OAI/NumberTheory/DirichletL/Hecke/Logarithmic.lean; sha256: 4e1a1a62c738c401b60aeeab30153debb383e156fc0afdfd08757ed1e7f2dd66 -/
section Source695
namespace OAI

noncomputable section
open scoped Classical Topology
open Set Metric
namespace SevenEighths.HeckeLogarithmic
open HeckeFamily HeckeLogarithmicInput

def complexity (η : Character) (t : ℝ) : ℝ :=
  2*(η.modulus.absNorm : ℝ)*(3+|t|)^2

theorem complexity_ge_exp (η : Character) (t : ℝ) : Real.exp 1 ≤ complexity η t :=
  LogarithmicControl.conductor_height_scale_ge_exp _ t (modulus_norm_ge_one η)

theorem regular_disk_differentiable (η : Character) {a e t : ℝ}
    (ha : (1/2 : ℝ) ≤ a) (he : 0 < e) :
    DifferentiableOn ℂ (regular η) (ball ((2 : ℂ)+t*Complex.I) (2-a-2*e)) := by
  intro z hz
  exact (regular_differentiableAt η (by
    have hr := LogarithmicControl.disk_re_gt hz
    linarith)).differentiableWithinAt

theorem exists_uniform_polynomial_exponent :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (η : Character), FiniteFourier.IsPrimitiveOnIdeals η.residue →
      ∀ a e t : ℝ, 1/2 ≤ a → 0 < e → ∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-3*e),
        ‖regular η z‖ ≤ (complexity η t)^M := by
  obtain ⟨M, hM, hb⟩ := LogarithmicControl.absorb_polynomial_constant
    (K := 2*uniformConstant) (p := 1) (by norm_num)
  refine ⟨M, hM, ?_⟩
  intro η hp a e t ha he z hz
  have hz2 : z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-2*e) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)) hz
  have h := regular_disk_growth η hp a e t ha he.le hz2
  have hQ : (η.modulus.absNorm : ℝ)^(3/5 : ℝ) ≤ (η.modulus.absNorm : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (modulus_norm_ge_one η)
      (show (3/5 : ℝ)≤1 by norm_num)
  apply h.trans
  calc
    _ ≤ (4*uniformConstant)*(η.modulus.absNorm : ℝ)*(3+|t|)^2 := by
      gcongr
      exact mul_nonneg (by norm_num) uniformConstant_nonneg
    _ = (2*uniformConstant)*complexity η t := by unfold complexity; ring
    _ ≤ (complexity η t)^M := by simpa only [Real.rpow_one] using hb _ (complexity_ge_exp η t)

theorem disk_control_of_euler_log (e A ε : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (hA : 1 ≤ A) (hε : 0 < ε) :
    ∃ D B : ℝ, 0 < D ∧ 0 ≤ B ∧ ∀ (η : Character),
      FiniteFourier.IsPrimitiveOnIdeals η.residue → ∀ (a t : ℝ) (E : ℂ → ℂ),
      1/2 ≤ a → a ≤ 1 →
      (∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), regular η z ≠ 0) →
      DifferentiableOn ℂ E (ball ((2 : ℂ)+t*Complex.I) (1/2)) →
      EqOn (Complex.exp ∘ E) (regular η) (ball ((2 : ℂ)+t*Complex.I) (1/2)) →
      (∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (49/100), ‖E z‖ ≤ A) →
      (∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-6*e),
        ‖regular η z‖ + ‖(regular η z)⁻¹‖ ≤ D*(complexity η t)^ε) ∧
      (∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-8*e),
        ‖deriv (regular η) z / regular η z‖ ≤ B*Real.log (complexity η t)) := by
  obtain ⟨M,hM,hpoly⟩ := exists_uniform_polynomial_exponent
  obtain ⟨D,hD,hb⟩ := LogarithmicControl.logarithmic_control he he' hA hM hε
  refine ⟨D, LogarithmicControl.outerConstant e A M/(2*e), hD, ?_, ?_⟩
  · have hB := LogarithmicControl.outerConstant_ge_one he he' hA hM
    positivity
  · intro η hp a t E ha ha' hzero hE hEL hEb
    exact hb a (complexity η t) (regular η) E ((2 : ℂ)+t*Complex.I) ha ha'
      (complexity_ge_exp η t) (regular_disk_differentiable η ha he) hzero
      (hpoly η hp a e t ha he) hE hEL hEb

end SevenEighths.HeckeLogarithmic

end

end OAI

end Source695

/- Original source: OAI/NumberTheory/DirichletL/Hecke/EulerLog.lean; sha256: d113d222250a1a98c35416261b399b80577a20e2f2ca8ae1ce5897806e6371d9 -/
section Source696
namespace OAI

noncomputable section
open scoped Classical Topology BigOperators
open Set Metric Filter Complex ActualEisensteinCubic
open SevenEighths.IdealEuler SevenEighths.IdealCharacter
open SmoothMobiusCorrection (PrimeIdeal)

namespace SevenEighths.HeckeEulerLog

def eulerLog (a : Ideal O →*₀ ℂ) (s : ℂ) : ℂ :=
  ∑' P : PrimeIdeal, -Complex.log (1 - weighted a s P.val)

def majorant (σ : ℝ) (P : PrimeIdeal) : ℝ :=
  (3 / 2) * (Ideal.absNorm P.val : ℝ) ^ (-σ)

theorem majorant_summable {σ : ℝ} (hσ : 1 < σ) : Summable (majorant σ) := by
  have h := (SmoothMobiusCorrection.prime_norm_series_summable (σ - 1)
    (by linarith)).mul_left (3 / 2)
  convert h using 1
  ext P
  unfold majorant
  congr 2
  ring

theorem weighted_norm_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (P : PrimeIdeal) {s : ℂ} {σ : ℝ} (hs : σ ≤ s.re) :
    ‖weighted a s P.val‖ ≤ (Ideal.absNorm P.val : ℝ) ^ (-σ) := by
  change ‖a P.val * CubicEisenstein.fullIdealWeight s P.val‖ ≤ _
  simp only [CubicEisenstein.fullIdealWeight, P.property.ne_zero, ite_false, norm_mul]
  change ‖a P.val‖ * ‖SmoothMobiusCorrection.primeNormPower P s‖ ≤ _
  rw [SmoothMobiusCorrection.norm_primeNormPower]
  have hn : (1 : ℝ) ≤ Ideal.absNorm P.val := by
    exact_mod_cast (show 1 ≤ Ideal.absNorm P.val from
      (by have := SmoothMobiusCorrection.prime_norm_two_le P; omega))
  exact (mul_le_of_le_one_left (by positivity) (ha _)).trans
    (Real.rpow_le_rpow_of_exponent_le hn (neg_le_neg hs))

theorem weighted_norm_le_half (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (P : PrimeIdeal) {s : ℂ} (hs : 1 ≤ s.re) : ‖weighted a s P.val‖ ≤ 1 / 2 := by
  refine (weighted_norm_le a ha P hs).trans ?_
  rw [Real.rpow_neg_one]
  have hn : (2 : ℝ) ≤ Ideal.absNorm P.val := by
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P
  exact inv_le_of_inv_le₀ (by norm_num) (by norm_num at *; exact hn)

theorem log_factor_norm_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (P : PrimeIdeal) {s : ℂ} {σ : ℝ} (hσ : 1 ≤ σ) (hs : σ ≤ s.re) :
    ‖-Complex.log (1 - weighted a s P.val)‖ ≤ majorant σ P := by
  have hhalf := weighted_norm_le_half a ha P (hσ.trans hs)
  have h := Complex.norm_log_one_add_half_le_self
    (z := -weighted a s P.val) (by simpa using hhalf)
  simp only [norm_neg, ← sub_eq_add_neg] at h ⊢
  exact h.trans (mul_le_mul_of_nonneg_left (weighted_norm_le a ha P hs) (by norm_num))

theorem weighted_differentiable (a : Ideal O →*₀ ℂ) (P : PrimeIdeal) :
    Differentiable ℂ (fun s ↦ weighted a s P.val) := by
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by
    exact_mod_cast (SmoothMobiusCorrection.prime_norm_pos P).ne'
  change Differentiable ℂ (fun s ↦ a P.val * CubicEisenstein.fullIdealWeight s P.val)
  simp only [CubicEisenstein.fullIdealWeight, P.property.ne_zero, ite_false]
  exact (differentiable_id.neg.const_cpow (Or.inl hn)).const_mul _

theorem log_factor_differentiableOn (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (P : PrimeIdeal) :
    DifferentiableOn ℂ (fun s ↦ -Complex.log (1 - weighted a s P.val)) {s : ℂ | 1 < s.re} := by
  intro s hs
  change 1 < s.re at hs
  have hn := prime_norm_lt_one a ha s (by linarith : 0 < s.re) P
  have hslit : 1 - weighted a s P.val ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one
      (z := -weighted a s P.val) (by simpa using hn)
  exact ((Complex.differentiableAt_log hslit).comp s
    ((differentiableAt_const (1 : ℂ)).sub (weighted_differentiable a P s))).neg.differentiableWithinAt

theorem eulerLog_differentiableOn_halfplane (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    {σ : ℝ} (hσ : 1 < σ) : DifferentiableOn ℂ (eulerLog a) {s : ℂ | σ < s.re} := by
  apply Complex.differentiableOn_tsum_of_summable_norm (majorant_summable hσ)
  · intro P
    exact (log_factor_differentiableOn a ha P).mono (fun s hs ↦ hσ.trans hs)
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro P s hs
    exact log_factor_norm_le a ha P hσ.le hs.le

theorem eulerLog_differentiableOn (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) :
    DifferentiableOn ℂ (eulerLog a) {s : ℂ | 1 < s.re} := by
  intro s hs
  change 1 < s.re at hs
  have hσ : 1 < (1 + s.re) / 2 := by linarith
  have hmem : s ∈ {w : ℂ | (1 + s.re) / 2 < w.re} := by dsimp; linarith
  exact ((eulerLog_differentiableOn_halfplane a ha hσ s hmem).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem)).differentiableWithinAt

theorem exp_eulerLog_eq_series (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : Complex.exp (eulerLog a s) = series a s :=
  SevenEighths.HeckeBoundary.exp_log_euler_eq_series a ha s hs

def eulerLogBound : ℝ := 1 + ∑' P : PrimeIdeal, majorant (3 / 2) P

theorem eulerLogBound_ge_one : 1 ≤ eulerLogBound := by
  unfold eulerLogBound
  have h : 0 ≤ ∑' P : PrimeIdeal, majorant (3 / 2) P :=
    tsum_nonneg (fun P ↦ by unfold majorant; positivity)
  linarith

theorem eulerLog_norm_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖eulerLog a s‖ ≤ eulerLogBound := by
  have hb : ∀ P : PrimeIdeal, ‖-Complex.log (1 - weighted a s P.val)‖ ≤ majorant (3 / 2) P :=
    fun P ↦ log_factor_norm_le a ha P (by norm_num) hs
  have hsum := majorant_summable (by norm_num : (1 : ℝ) < 3 / 2)
  have hnorm : Summable (fun P : PrimeIdeal ↦ ‖-Complex.log (1 - weighted a s P.val)‖) :=
    hsum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hb
  calc
    ‖eulerLog a s‖ ≤ ∑' P : PrimeIdeal, ‖-Complex.log (1 - weighted a s P.val)‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' P : PrimeIdeal, majorant (3 / 2) P := hnorm.tsum_le_tsum hb hsum
    _ ≤ eulerLogBound := by unfold eulerLogBound; linarith

theorem inner_disk_re {t : ℝ} {s : ℂ}
    (hs : s ∈ closedBall (2 + (t : ℂ) * Complex.I) (1 / 2)) : 3 / 2 ≤ s.re := by
  have hn : ‖(2 + (t : ℂ) * Complex.I) - s‖ ≤ 1 / 2 := by
    simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hs
  have hr := Complex.re_le_norm ((2 + (t : ℂ) * Complex.I) - s)
  norm_num at hr
  linarith

theorem eulerLog_inner_disk (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) (t : ℝ) :
    DifferentiableOn ℂ (eulerLog a) (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      EqOn (Complex.exp ∘ eulerLog a) (series a)
        (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      ∀ s ∈ closedBall (2 + (t : ℂ) * Complex.I) (49 / 100),
        ‖eulerLog a s‖ ≤ eulerLogBound := by
  have hsub : ball (2 + (t : ℂ) * Complex.I) (1 / 2) ⊆ {s : ℂ | 1 < s.re} := by
    intro s hs
    have := inner_disk_re (ball_subset_closedBall hs)
    change 1 < s.re
    linarith
  refine ⟨(eulerLog_differentiableOn a ha).mono hsub, ?_, ?_⟩
  · intro s hs
    exact exp_eulerLog_eq_series a ha s (hsub hs)
  · intro s hs
    exact eulerLog_norm_le a ha (inner_disk_re (closedBall_subset_closedBall (by norm_num) hs))

theorem continued_inner_disk (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (L : ℂ → ℂ) (hL : ∀ s : ℂ, 1 < s.re → L s = series a s) (t : ℝ) :
    DifferentiableOn ℂ (eulerLog a) (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      EqOn (Complex.exp ∘ eulerLog a) L (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      ∀ s ∈ closedBall (2 + (t : ℂ) * Complex.I) (49 / 100),
        ‖eulerLog a s‖ ≤ eulerLogBound := by
  obtain ⟨hd, he, hb⟩ := eulerLog_inner_disk a ha t
  refine ⟨hd, ?_, hb⟩
  intro s hs
  have hr := inner_disk_re (ball_subset_closedBall hs)
  exact (he hs).trans (hL s (by linarith)).symm

def principalLog (s : ℂ) : ℂ := Complex.log (1 - 2 / (s + 1))

theorem norm_two_div_add_one_lt_one {s : ℂ} (hs : 1 < s.re) :
    ‖(2 : ℂ) / (s + 1)‖ < 1 := by
  have hr := Complex.re_le_norm (s + 1)
  norm_num at hr
  have hn : 0 < ‖s + 1‖ := by linarith
  rw [norm_div]
  norm_num only [Complex.norm_ofNat]
  exact (div_lt_one hn).mpr (by linarith)

theorem norm_two_div_add_one_le {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    ‖(2 : ℂ) / (s + 1)‖ ≤ 4 / 5 := by
  have hr := Complex.re_le_norm (s + 1)
  norm_num at hr
  have hn : 0 < ‖s + 1‖ := by linarith
  rw [norm_div]
  norm_num only [Complex.norm_ofNat]
  exact (div_le_iff₀ hn).mpr (by linarith)

theorem principalLog_differentiableOn :
    DifferentiableOn ℂ principalLog {s : ℂ | 1 < s.re} := by
  intro s hs
  change 1 < s.re at hs
  have hnorm := norm_two_div_add_one_lt_one hs
  have hslit : 1 - (2 : ℂ) / (s + 1) ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg, neg_div] using Complex.mem_slitPlane_of_norm_lt_one
      (z := -(2 : ℂ) / (s + 1)) (by simpa using hnorm)
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  exact ((Complex.differentiableAt_log hslit).comp s
    ((differentiableAt_const (1 : ℂ)).sub ((differentiableAt_const (2 : ℂ)).div
      (differentiableAt_id.add_const 1) hs1))).differentiableWithinAt

theorem exp_principalLog {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (principalLog s) = (s - 1) / (s + 1) := by
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  rw [principalLog, Complex.exp_log (SmoothMobiusCorrection.one_sub_ne_zero
    (norm_two_div_add_one_lt_one hs))]
  field_simp
  ring

theorem principalLog_norm_le {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖principalLog s‖ ≤ 3 := by
  have hb := norm_two_div_add_one_le hs
  have hlt : ‖-(2 : ℂ) / (s + 1)‖ < 1 := by simpa using hb.trans_lt (by norm_num : (4 : ℝ) / 5 < 1)
  have h := Complex.norm_log_one_add_le hlt
  have hn : ‖-(2 : ℂ) / (s + 1)‖ = ‖(2 : ℂ) / (s + 1)‖ := by simp
  rw [hn] at h
  have heq : 1 + -(2 : ℂ) / (s + 1) = 1 - 2 / (s + 1) := by ring
  rw [heq] at h
  change ‖principalLog s‖ ≤ _ at h
  have hden : 0 < 1 - ‖(2 : ℂ) / (s + 1)‖ := by linarith
  have hinv : (1 - ‖(2 : ℂ) / (s + 1)‖)⁻¹ ≤ 5 := by
    rw [inv_eq_one_div, div_le_iff₀ hden]
    linarith
  have hnorm := norm_nonneg ((2 : ℂ) / (s + 1))
  have hsq : ‖(2 : ℂ) / (s + 1)‖ ^ 2 ≤ 16 / 25 := by nlinarith
  have hmul := mul_le_mul hsq hinv (inv_nonneg.mpr hden.le) (by norm_num : (0 : ℝ) ≤ 16 / 25)
  nlinarith

def principalEulerLog (a : Ideal O →*₀ ℂ) (s : ℂ) : ℂ := principalLog s + eulerLog a s

theorem principalEulerLog_differentiableOn (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) :
    DifferentiableOn ℂ (principalEulerLog a) {s : ℂ | 1 < s.re} :=
  principalLog_differentiableOn.add (eulerLog_differentiableOn a ha)

theorem exp_principalEulerLog (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (principalEulerLog a s) = ((s - 1) / (s + 1)) * series a s := by
  rw [principalEulerLog, Complex.exp_add, exp_principalLog hs, exp_eulerLog_eq_series a ha s hs]

theorem principalEulerLog_norm_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖principalEulerLog a s‖ ≤ 3 + eulerLogBound :=
  (norm_add_le _ _).trans (add_le_add (principalLog_norm_le hs) (eulerLog_norm_le a ha hs))

theorem principal_continued_inner_disk (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (L : ℂ → ℂ)
    (hL : ∀ s : ℂ, 1 < s.re → L s = ((s - 1) / (s + 1)) * series a s) (t : ℝ) :
    DifferentiableOn ℂ (principalEulerLog a) (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      EqOn (Complex.exp ∘ principalEulerLog a) L
        (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      ∀ s ∈ closedBall (2 + (t : ℂ) * Complex.I) (49 / 100),
        ‖principalEulerLog a s‖ ≤ 3 + eulerLogBound := by
  have hsub : ball (2 + (t : ℂ) * Complex.I) (1 / 2) ⊆ {s : ℂ | 1 < s.re} := by
    intro s hs
    have := inner_disk_re (ball_subset_closedBall hs)
    change 1 < s.re
    linarith
  refine ⟨(principalEulerLog_differentiableOn a ha).mono hsub, ?_, ?_⟩
  · intro s hs
    exact (exp_principalEulerLog a ha (hsub hs)).trans (hL s (hsub hs)).symm
  · intro s hs
    exact principalEulerLog_norm_le a ha
      (inner_disk_re (closedBall_subset_closedBall (by norm_num) hs))

theorem residue_continued_inner_disk (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (L : ℂ → ℂ)
    (hL : ∀ s : ℂ, 1 < s.re → L s = series (ofResidue M χ hχ) s) (t : ℝ) :
    DifferentiableOn ℂ (eulerLog (ofResidue M χ hχ))
        (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      EqOn (Complex.exp ∘ eulerLog (ofResidue M χ hχ)) L
        (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      ∀ s ∈ closedBall (2 + (t : ℂ) * Complex.I) (49 / 100),
        ‖eulerLog (ofResidue M χ hχ) s‖ ≤ eulerLogBound :=
  continued_inner_disk _ (norm_ofResidue_le_one M χ hχ) L hL t

theorem continued_logarithmic_control {e M ε : ℝ}
    (he : 0 < e) (he' : e < 1 / 1000) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (b C t : ℝ) (a : Ideal O →*₀ ℂ),
      (∀ I, ‖a I‖ ≤ 1) → ∀ L : ℂ → ℂ,
      1 / 2 ≤ b → b ≤ 1 → Real.exp 1 ≤ C →
      (∀ s : ℂ, 1 < s.re → L s = series a s) →
      DifferentiableOn ℂ L (ball (2 + (t : ℂ) * Complex.I) (2 - b - 2 * e)) →
      (∀ z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - b - 2 * e), L z ≠ 0) →
      (∀ z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - b - 3 * e), ‖L z‖ ≤ C ^ M) →
      (∀ z ∈ closedBall (2 + (t : ℂ) * Complex.I) (2 - b - 6 * e),
        ‖L z‖ + ‖(L z)⁻¹‖ ≤ D * C ^ ε) ∧
      (∀ z ∈ closedBall (2 + (t : ℂ) * Complex.I) (2 - b - 8 * e),
        ‖deriv L z / L z‖ ≤
          (LogarithmicControl.outerConstant e eulerLogBound M / (2 * e)) * Real.log C) := by
  obtain ⟨D, hD, hbound⟩ := LogarithmicControl.logarithmic_control he he'
    eulerLogBound_ge_one hM hε
  refine ⟨D, hD, ?_⟩
  intro b C t a ha L hb hb' hC hEq hL h0 hp
  obtain ⟨hE, heq, hEb⟩ := continued_inner_disk a ha L hEq t
  exact hbound b C L (eulerLog a) (2 + (t : ℂ) * Complex.I)
    hb hb' hC hL h0 hp hE heq hEb

theorem principal_continued_logarithmic_control {e M ε : ℝ}
    (he : 0 < e) (he' : e < 1 / 1000) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (b C t : ℝ) (a : Ideal O →*₀ ℂ),
      (∀ I, ‖a I‖ ≤ 1) → ∀ L : ℂ → ℂ,
      1 / 2 ≤ b → b ≤ 1 → Real.exp 1 ≤ C →
      (∀ s : ℂ, 1 < s.re → L s = ((s - 1) / (s + 1)) * series a s) →
      DifferentiableOn ℂ L (ball (2 + (t : ℂ) * Complex.I) (2 - b - 2 * e)) →
      (∀ z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - b - 2 * e), L z ≠ 0) →
      (∀ z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - b - 3 * e), ‖L z‖ ≤ C ^ M) →
      (∀ z ∈ closedBall (2 + (t : ℂ) * Complex.I) (2 - b - 6 * e),
        ‖L z‖ + ‖(L z)⁻¹‖ ≤ D * C ^ ε) ∧
      (∀ z ∈ closedBall (2 + (t : ℂ) * Complex.I) (2 - b - 8 * e),
        ‖deriv L z / L z‖ ≤
          (LogarithmicControl.outerConstant e (3 + eulerLogBound) M / (2 * e)) * Real.log C) := by
  have hA : 1 ≤ 3 + eulerLogBound := by linarith [eulerLogBound_ge_one]
  obtain ⟨D, hD, hbound⟩ := LogarithmicControl.logarithmic_control he he' hA hM hε
  refine ⟨D, hD, ?_⟩
  intro b C t a ha L hb hb' hC hEq hL h0 hp
  obtain ⟨hE, heq, hEb⟩ := principal_continued_inner_disk a ha L hEq t
  exact hbound b C L (principalEulerLog a) (2 + (t : ℂ) * Complex.I)
    hb hb' hC hL h0 hp hE heq hEb

end SevenEighths.HeckeEulerLog

end

end OAI

end Source696

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DeletionBounds.lean; sha256: 129624cafbac617ee0288024f623cc81fec9f7b16e8b5f4adc0c4890f83fde6b -/
section Source697
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDeletionBounds
open HeckeFamily

theorem constant_pow_primeSupport_bound (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Ideal O, M ≠ ⊥ →
      K^(IdealMobiusDivisorSum.primeSupport M).card ≤ C*(M.absNorm : ℝ)^ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max K 1)
  have hn0 : 0 < (n : ℝ) := by linarith [le_max_right K 1]
  have hKpow : K ≤ (2 : ℝ)^n := by
    have hn2 : (n : ℝ) ≤ (2 : ℝ)^n := by exact_mod_cast (show n < 2^n from Nat.lt_two_pow_self).le
    linarith [le_max_left K 1]
  obtain ⟨C, hC, hbound⟩ := SquarefreeDivisorBound.prime_support_subsets_bound
    (ε/(n : ℝ)) (div_pos hε hn0)
  refine ⟨C^n, by positivity, ?_⟩
  intro M hM
  calc
    _ ≤ ((2 : ℝ)^n)^(IdealMobiusDivisorSum.primeSupport M).card :=
      pow_le_pow_left₀ hK hKpow _
    _ = ((2 : ℝ)^(IdealMobiusDivisorSum.primeSupport M).card)^n := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ (C*(M.absNorm : ℝ)^(ε/(n : ℝ)))^n :=
      pow_le_pow_left₀ (by positivity) (hbound M hM) n
    _ = C^n*(M.absNorm : ℝ)^ε := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity), div_mul_cancel₀ _ hn0.ne']

def localBound (σ : ℝ) : ℝ := (1-(2 : ℝ)^(-σ))⁻¹

theorem localBound_pos {σ : ℝ} (hσ : 0 < σ) : 0 < localBound σ := by
  unfold localBound
  exact inv_pos.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)))

theorem term_bound {σ N : ℝ} (hσ : 0 < σ) (hN : 2 ≤ N)
    {a s : ℂ} (ha : ‖a‖ ≤ 1) (hs : σ ≤ s.re) :
    ‖a*(N : ℂ)^(-s)‖ ≤ (2 : ℝ)^(-σ) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < N), Complex.neg_re]
  apply (mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) _) ha).trans
  apply (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ N) (by linarith : -s.re ≤ -σ)).trans
  exact Real.rpow_le_rpow_of_nonpos (by norm_num) hN (by linarith)

theorem factor_bounds {σ N : ℝ} (hσ : 0 < σ) (hN : 2 ≤ N)
    {a s : ℂ} (ha : ‖a‖ ≤ 1) (hs : σ ≤ s.re) :
    ‖EulerFactors.factor N a s‖ ≤ localBound σ ∧
      ‖(EulerFactors.factor N a s)⁻¹‖ ≤ localBound σ := by
  have hδ : (2 : ℝ)^(-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hδ0 : 0 ≤ (2 : ℝ)^(-σ) := Real.rpow_nonneg (by norm_num) _
  have ht := term_bound hσ hN ha hs
  have hl : 1-(2 : ℝ)^(-σ) ≤ ‖EulerFactors.factor N a s‖ := by
    have hh := norm_sub_le (1-a*(N : ℂ)^(-s)) (-a*(N : ℂ)^(-s))
    have he : (1-a*(N : ℂ)^(-s))-(-a*(N : ℂ)^(-s)) = 1 := by ring
    rw [he, norm_one, neg_mul, norm_neg] at hh
    change 1-(2 : ℝ)^(-σ) ≤ ‖1-a*(N : ℂ)^(-s)‖
    linarith
  constructor
  · apply (norm_sub_le _ _).trans
    rw [norm_one]
    apply (add_le_add (le_refl 1) ht).trans
    unfold localBound
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by linarith : 0 < 1-(2 : ℝ)^(-σ))).mpr
    nlinarith [sq_nonneg ((2 : ℝ)^(-σ))]
  · rw [norm_inv]
    exact (inv_le_inv₀ (by linarith : 0 < ‖EulerFactors.factor N a s‖)
      (by linarith : 0 < 1-(2 : ℝ)^(-σ))).mpr hl

theorem factors_bound_pow (σ : ℝ) (hσ : 0 < σ) (M : Ideal O)
    (ψ : Character) {s : ℂ} (hs : σ ≤ s.re) :
    ‖HeckeFiniteDeletion.factors M ψ s‖ ≤
      (localBound σ)^(IdealMobiusDivisorSum.primeSupport M).card ∧
    ‖(HeckeFiniteDeletion.factors M ψ s)⁻¹‖ ≤
      (localBound σ)^(IdealMobiusDivisorSum.primeSupport M).card := by
  have hfactor (P : SmoothMobiusCorrection.PrimeIdeal) :
      ‖EulerFactors.factor (P.val.absNorm : ℝ) (idealCoeff ψ P.val) s‖ ≤ localBound σ ∧
      ‖(EulerFactors.factor (P.val.absNorm : ℝ) (idealCoeff ψ P.val) s)⁻¹‖ ≤ localBound σ :=
    factor_bounds hσ (by exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P)
      (idealCoeff_norm_le_one ψ P.val) hs
  have he : (∏ P ∈ SmoothMobiusCorrection.primeSet M, localBound σ) =
      (localBound σ)^(IdealMobiusDivisorSum.primeSupport M).card := by
    rw [SmoothMobiusCorrection.prod_primeSet M (fun _ => localBound σ)]
    simp
  constructor
  · unfold HeckeFiniteDeletion.factors EulerFactors.deletedProduct
    rw [norm_prod, ← he]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun P _ => (hfactor P).1)
  · unfold HeckeFiniteDeletion.factors EulerFactors.deletedProduct
    rw [← Finset.prod_inv_distrib, norm_prod, ← he]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun P _ => (hfactor P).2)

theorem factors_subpower_bound (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal O), M ≠ ⊥ → ∀ (ψ : Character) (s : ℂ),
      σ ≤ s.re → ‖HeckeFiniteDeletion.factors M ψ s‖ +
        ‖(HeckeFiniteDeletion.factors M ψ s)⁻¹‖ ≤ C*(M.absNorm : ℝ)^ε := by
  obtain ⟨C, hC, hb⟩ := constant_pow_primeSupport_bound (localBound σ) ε
    (localBound_pos hσ).le hε
  refine ⟨2*C, by positivity, ?_⟩
  intro M hM ψ s hs
  obtain ⟨h1, h2⟩ := factors_bound_pow σ hσ M ψ hs
  have h := hb M hM
  nlinarith

def radical (M : Ideal O) : Ideal O :=
  SmoothMobiusCorrection.primeProduct (SmoothMobiusCorrection.primeSet M)

theorem radical_ne_zero (M : Ideal O) : radical M ≠ 0 :=
  SmoothMobiusCorrection.primeProduct_ne_zero _

theorem factors_radical (M : Ideal O) (ψ : Character) (s : ℂ) :
    HeckeFiniteDeletion.factors (radical M) ψ s = HeckeFiniteDeletion.factors M ψ s := by
  unfold HeckeFiniteDeletion.factors radical
  rw [SmoothMobiusCorrection.primeSet_primeProduct]

theorem factors_radical_subpower_bound (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal O) (ψ : Character) (s : ℂ),
      σ ≤ s.re → ‖HeckeFiniteDeletion.factors M ψ s‖ +
        ‖(HeckeFiniteDeletion.factors M ψ s)⁻¹‖ ≤ C*((radical M).absNorm : ℝ)^ε := by
  obtain ⟨C, hC, hb⟩ := factors_subpower_bound σ ε hσ hε
  refine ⟨C, hC, ?_⟩
  intro M ψ s hs
  simpa only [factors_radical] using hb (radical M) (radical_ne_zero M) ψ s hs

theorem factor_bound_any_re {N : ℝ} (hN : 2 ≤ N) {a s : ℂ} (ha : ‖a‖ ≤ 1) :
    ‖EulerFactors.factor N a s‖ ≤ 2*N^(max (-s.re) 0) := by
  have hn : 1 ≤ N := by linarith
  have ht : ‖a*(N : ℂ)^(-s)‖ ≤ N^(-s.re) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < N), Complex.neg_re]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) _) ha
  have hpow : N^(-s.re) ≤ N^(max (-s.re) 0) :=
    Real.rpow_le_rpow_of_exponent_le hn (le_max_left _ _)
  have h1 : 1 ≤ N^(max (-s.re) 0) := Real.one_le_rpow hn (le_max_right _ _)
  have hb := norm_sub_le (1 : ℂ) (a*(N : ℂ)^(-s))
  rw [norm_one] at hb
  change ‖1-a*(N : ℂ)^(-s)‖ ≤ _
  linarith

theorem factors_bound_any_re (M : Ideal O) (ψ : Character) (s : ℂ) :
    ‖HeckeFiniteDeletion.factors M ψ s‖ ≤
      (2 : ℝ)^(SmoothMobiusCorrection.primeSet M).card *
        ((radical M).absNorm : ℝ)^(max (-s.re) 0) := by
  unfold HeckeFiniteDeletion.factors EulerFactors.deletedProduct
  rw [norm_prod]
  calc
    _ ≤ ∏ P ∈ SmoothMobiusCorrection.primeSet M,
        2*(P.val.absNorm : ℝ)^(max (-s.re) 0) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro P _
      exact factor_bound_any_re (show (2 : ℝ) ≤ (P.val.absNorm : ℝ) by exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P)
        (idealCoeff_norm_le_one ψ P.val)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const,
        Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
      simp only [radical, SmoothMobiusCorrection.primeProduct, map_prod, Nat.cast_prod]

theorem primeSet_card (M : Ideal O) :
    (SmoothMobiusCorrection.primeSet M).card =
      (IdealMobiusDivisorSum.primeSupport M).card := by
  unfold SmoothMobiusCorrection.primeSet
  rw [Finset.card_image_iff.mpr ?_, Finset.card_attach]
  intro P hP Q hQ h
  exact Subtype.ext (congrArg (fun R : SmoothMobiusCorrection.PrimeIdeal => R.val) h)

theorem factors_any_re_subpower_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal O) (ψ : Character) (s : ℂ),
      ‖HeckeFiniteDeletion.factors M ψ s‖ ≤
        C*((radical M).absNorm : ℝ)^(max (-s.re) 0 + ε) := by
  obtain ⟨C, hC, hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro M ψ s
  have hR : 0 < ((radical M).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero M))
  have hc : (2 : ℝ)^(SmoothMobiusCorrection.primeSet M).card ≤ C*((radical M).absNorm : ℝ)^ε := by
    have h := hb (radical M) (radical_ne_zero M)
    rw [← primeSet_card, radical, SmoothMobiusCorrection.primeSet_primeProduct] at h
    exact h
  apply (factors_bound_any_re M ψ s).trans
  calc
    _ ≤ (C*((radical M).absNorm : ℝ)^ε)*((radical M).absNorm : ℝ)^(max (-s.re) 0) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hR.le _)
    _ = _ := by rw [Real.rpow_add hR]; ring

end SevenEighths.HeckeDeletionBounds

end

end OAI

end Source697

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DeletionReciprocal.lean; sha256: 337a0e05e48896e92f7d19223c96c1225dfcb72111cc1b9394cba10f775e87ea -/
section Source698
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDeletionReciprocal
open HeckeFamily HeckeFiniteDeletion HeckeReciprocal HeckeDeletionBounds

theorem reciprocal_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) :
    reciprocal χ s = reciprocal ψ s * (factors χ.modulus ψ s)⁻¹ := by
  by_cases hχ : χ.residue = 1
  · have hψ := (principal_iff_of_mask χ ψ hmask).mp hχ
    simp only [reciprocal, ite_eq_left hχ, ite_eq_left hψ]
    rw [regularizedL_eq_of_mask χ ψ hmask hs]
    ring
  · have hψ : ψ.residue ≠ 1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
    simp only [reciprocal, ite_eq_right hχ, ite_eq_right hψ]
    rw [LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hs, mul_inv]

theorem exists_primitive_reciprocal_reduction (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ χ : Character,
      ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
        ψ.modulus.absNorm ≤ χ.modulus.absNorm ∧
        (∀ I : Ideal O, idealCoeff χ I =
          if IsCoprime I χ.modulus then idealCoeff ψ I else 0) ∧
        ∀ s : ℂ, σ ≤ s.re →
          ‖reciprocal χ s‖ ≤ C*((radical χ.modulus).absNorm : ℝ)^ε * ‖reciprocal ψ s‖ := by
  obtain ⟨C, hC, hb⟩ := factors_radical_subpower_bound σ ε hσ hε
  refine ⟨C, hC, ?_⟩
  intro χ
  obtain ⟨ψ, _, hp, hn, hm⟩ := exists_primitive_character χ
  refine ⟨ψ, hp, hn, hm, ?_⟩
  intro s hs
  rw [reciprocal_eq_of_mask χ ψ hm (hσ.trans_le hs), norm_mul]
  have hf := hb χ.modulus ψ s hs
  have hfb : ‖(factors χ.modulus ψ s)⁻¹‖ ≤ C*((radical χ.modulus).absNorm : ℝ)^ε := by
    linarith [norm_nonneg (factors χ.modulus ψ s)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hfb (norm_nonneg (reciprocal ψ s))

end SevenEighths.HeckeDeletionReciprocal

end

end OAI

end Source698

/- Original source: OAI/NumberTheory/DirichletL/Hecke/LogarithmicActual.lean; sha256: 0de1032bf421966bd89b1f5da862315adfb6a45e78f4af937dcedf0698ac87b1 -/
section Source699
namespace OAI

noncomputable section
open scoped Classical Topology
open Set Metric
namespace SevenEighths.HeckeLogarithmicActual
open HeckeFamily HeckeLogarithmicInput HeckeLogarithmic

def eulerLog (η : Character) : ℂ → ℂ :=
  if η.residue = 1 then HeckeEulerLog.principalEulerLog (idealCoeff η)
  else HeckeEulerLog.eulerLog (idealCoeff η)

def innerBound : ℝ := 3+HeckeEulerLog.eulerLogBound

theorem innerBound_ge_one : 1 ≤ innerBound := by
  unfold innerBound
  linarith [HeckeEulerLog.eulerLogBound_ge_one]

theorem actual_inner_log (η : Character) (t : ℝ) :
    DifferentiableOn ℂ (eulerLog η) (ball ((2 : ℂ)+t*Complex.I) (1/2)) ∧
    EqOn (Complex.exp ∘ eulerLog η) (regular η) (ball ((2 : ℂ)+t*Complex.I) (1/2)) ∧
    ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (49/100), ‖eulerLog η z‖ ≤ innerBound := by
  by_cases hη : η.residue = 1
  · have hright (s : ℂ) (hs : 1<s.re) : regular η s =
        ((s-1)/(s+1))*IdealEuler.series (idealCoeff η) s := by
      have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
      have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
      simp only [regular, ite_eq_left hη, HeckePrincipalStrip.sourceNormalized]
      rw [HeckeOrigin.poleRemoved_eq η h0 h1, LFunction_eq_series η hs]
      ring
    simpa only [eulerLog, ite_eq_left hη, innerBound] using
      HeckeEulerLog.principal_continued_inner_disk (idealCoeff η) (idealCoeff_norm_le_one η)
        (regular η) hright t
  · have hright (s : ℂ) (hs : 1<s.re) : regular η s = IdealEuler.series (idealCoeff η) s := by
      rw [regular_eq_nonprincipal η hη]
      exact LFunction_eq_series η hs
    obtain ⟨hd,he,hb⟩ := HeckeEulerLog.continued_inner_disk (idealCoeff η)
      (idealCoeff_norm_le_one η) (regular η) hright t
    simp only [eulerLog, ite_eq_right hη]
    refine ⟨hd,he,?_⟩
    intro z hz
    have h := hb z hz
    unfold innerBound
    linarith

theorem disk_control (e ε : ℝ) (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ D B : ℝ, 0<D ∧ 0≤B ∧ ∀ (η : Character),
      FiniteFourier.IsPrimitiveOnIdeals η.residue → ∀ a t : ℝ,
      1/2≤a → a≤1 →
      (∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), regular η z ≠ 0) →
      (∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-6*e),
        ‖regular η z‖ + ‖(regular η z)⁻¹‖ ≤ D*(complexity η t)^ε) ∧
      (∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-8*e),
        ‖deriv (regular η) z / regular η z‖ ≤ B*Real.log (complexity η t)) := by
  obtain ⟨D,B,hD,hB,hb⟩ := disk_control_of_euler_log e innerBound ε he he' innerBound_ge_one hε
  refine ⟨D,B,hD,hB,?_⟩
  intro η hp a t ha ha' hzero
  obtain ⟨hE,hEL,hEb⟩ := actual_inner_log η t
  exact hb η hp a t (eulerLog η) ha ha' hzero hE hEL hEb

theorem primitive_reciprocal_subpower (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ D : ℝ, 0<D ∧ ∀ (η : Character), FiniteFourier.IsPrimitiveOnIdeals η.residue →
      ∀ s : ℂ, HeckeZeroSupremum.beta+8*e ≤ s.re →
        ‖HeckeReciprocal.reciprocal η s‖ ≤ D*(complexity η s.im)^ε := by
  obtain ⟨D,B,hD,_,hb⟩ := disk_control e ε he he' hε
  have hEuler : 0 ≤ HeckeReciprocalBound.bound 2 := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨D+HeckeReciprocalBound.bound 2, by linarith, ?_⟩
  intro η hp s hs
  have hcomp : 1 ≤ (complexity η s.im)^ε := Real.one_le_rpow
    ((Real.one_le_exp (by norm_num : (0 : ℝ)≤1)).trans (complexity_ge_exp η s.im)) hε.le
  by_cases hs2 : s.re ≤ 2
  · have hbound := (hb η hp HeckeZeroSupremum.beta s.im HeckeZeroSupremum.half_le_beta
      HeckeZeroSupremum.beta_le_one (fun z hz => regular_ne_zero_on_disk η HeckeZeroSupremum.beta e s.im le_rfl he hz)).1
    have hmem : s ∈ closedBall ((2 : ℂ)+s.im*Complex.I) (2-HeckeZeroSupremum.beta-6*e) := by
      have h := LogarithmicControl.same_height_mem_disk (a := HeckeZeroSupremum.beta)
        (e := e) (t := s.im) (v := 8*e) le_rfl hs hs2
      rw [Complex.re_add_im] at h
      exact closedBall_subset_closedBall (by linarith) h
    have hz := hbound s hmem
    have hr := reciprocal_norm_le_regular_inverse η (by linarith : HeckeZeroSupremum.beta<s.re)
    have hcp : 0 ≤ (complexity η s.im)^ε := by linarith
    nlinarith [norm_nonneg (regular η s)]
  · have hr := HeckeReciprocalBound.reciprocal_norm_le η (by norm_num : (1 : ℝ)<2)
      (le_of_not_ge hs2)
    have hp0 : 0 ≤ D+HeckeReciprocalBound.bound 2 := by linarith
    exact hr.trans ((by linarith : HeckeReciprocalBound.bound 2 ≤ D+HeckeReciprocalBound.bound 2).trans
      (le_mul_of_one_le_right hp0 hcomp))

end SevenEighths.HeckeLogarithmicActual

end

end OAI

end Source699

/- Original source: OAI/NumberTheory/DirichletL/Hecke/ReciprocalGrowth.lean; sha256: daaecdb8cc03b9067c3c82928f46ca8a6e01da05483df526a1048775e4384b8c -/
section Source700
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeReciprocalGrowth
open HeckeFamily HeckeLogarithmic HeckeDeletionBounds

def presentationComplexity (χ : Character) (t : ℝ) : ℝ :=
  ((radical χ.modulus).absNorm : ℝ)*complexity χ t

theorem reciprocal_subpower (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ D : ℝ, 0<D ∧ ∀ (χ : Character) (s : ℂ),
      HeckeZeroSupremum.beta+8*e ≤ s.re →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ D*(presentationComplexity χ s.im)^ε := by
  obtain ⟨Dp,hDp,hpbound⟩ := HeckeLogarithmicActual.primitive_reciprocal_subpower e ε he he' hε
  obtain ⟨Cd,hCd,hreduce⟩ := HeckeDeletionReciprocal.exists_primitive_reciprocal_reduction
    (HeckeZeroSupremum.beta+8*e) ε (by linarith [HeckeZeroSupremum.half_le_beta]) hε
  refine ⟨Cd*Dp, mul_pos hCd hDp, ?_⟩
  intro χ s hs
  obtain ⟨ψ,hp,hn,_,hr⟩ := hreduce χ
  have hc : complexity ψ s.im ≤ complexity χ s.im := by
    unfold complexity
    have hn' : (ψ.modulus.absNorm : ℝ) ≤ χ.modulus.absNorm := by exact_mod_cast hn
    gcongr
  have hc0 : 0 ≤ complexity ψ s.im :=
    (Real.exp_pos 1).le.trans (complexity_ge_exp ψ s.im)
  have hr0 : 0 ≤ ((radical χ.modulus).absNorm : ℝ) := by positivity
  apply (hr s hs).trans
  calc
    _ ≤ Cd*((radical χ.modulus).absNorm : ℝ)^ε * (Dp*(complexity ψ s.im)^ε) :=
      mul_le_mul_of_nonneg_left (hpbound ψ hp s hs) (by positivity)
    _ = (Cd*Dp)*(((radical χ.modulus).absNorm : ℝ)*complexity ψ s.im)^ε := by
      rw [Real.mul_rpow hr0 hc0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg hr0 hc0) (mul_le_mul_of_nonneg_left hc hr0) hε.le)
      (mul_pos hCd hDp).le

theorem polynomial_reciprocal_bound (χ : Character) (a : ℝ)
    (hβ : HeckeZeroSupremum.beta < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2) := by
  let e : ℝ := min (1/2000) ((a-HeckeZeroSupremum.beta)/16)
  have he : 0<e := lt_min (by norm_num) (by linarith)
  have he' : e<1/1000 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hmargin : HeckeZeroSupremum.beta+8*e ≤ a := by
    have hh := min_le_right (1/2000 : ℝ) ((a-HeckeZeroSupremum.beta)/16)
    change e ≤ (a-HeckeZeroSupremum.beta)/16 at hh
    linarith
  obtain ⟨C,hC,hbound⟩ := reciprocal_subpower e 1 he he' (by norm_num)
  let K : ℝ := C*((radical χ.modulus).absNorm : ℝ)*(2*(χ.modulus.absNorm : ℝ))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨18*K, by positivity, ?_⟩
  intro s hs
  have h := hbound χ s (hmargin.trans hs)
  have hheight : (3+|s.im|)^2 ≤ 18*(1+|s.im|^2) := by
    nlinarith [sq_nonneg (|s.im|-1), sq_nonneg |s.im|]
  rw [Real.rpow_one] at h
  calc
    _ ≤ K*(3+|s.im|)^2 := by
      convert h using 1 ; unfold K presentationComplexity complexity ; ring
    _ ≤ K*(18*(1+|s.im|^2)) := mul_le_mul_of_nonneg_left hheight hK
    _ = _ := by ring

end SevenEighths.HeckeReciprocalGrowth

end

end OAI

end Source700

/- Original source: OAI/NumberTheory/DirichletL/Detector.lean; sha256: b7a35ece30047890b1ae79cad9d6ef11ba15c8d377086e940cc54c0e8401ff67 -/
section Source701
namespace OAI

namespace SevenEighths.Detector

theorem exists_small_increment (M : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    {lo hi e : ℝ} (hlo : lo ≤ M 0) (hhi : M n ≤ hi)
    (hwidth : hi - lo ≤ n * e) :
    ∃ i < n, M (i + 1) - M i ≤ e := by
  by_contra h
  have hinc : ∀ i ∈ Finset.range n, e < M (i + 1) - M i := by
    intro i hi
    exact lt_of_not_ge (fun hle => h ⟨i, Finset.mem_range.mp hi, hle⟩)
  have hs := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hn)) hinc
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Finset.sum_range_sub] at hs
  linarith

theorem buffered_bin_of_rounding {x y a e : ℝ}
    (hround : a ≤ x ∧ x < a + e) (hstep : y - x ≤ e) :
    a ≤ x ∧ x < a + e ∧ y < a + 2 * e := by
  exact ⟨hround.1, hround.2, by linarith [hround.2]⟩

theorem exists_grid_rounding {base x e : ℝ} (he : 0 < e) (hx : base ≤ x) :
    ∃ k : ℕ, base + e * k ≤ x ∧ x < base + e * k + e := by
  let k := ⌊(x - base) / e⌋₊
  have hnonneg : 0 ≤ (x - base) / e := div_nonneg (sub_nonneg.mpr hx) he.le
  have hlo := Nat.floor_le hnonneg
  have hhi := Nat.lt_floor_add_one ((x - base) / e)
  have hlo' := (le_div_iff₀ he).mp hlo
  have hhi' := (div_lt_iff₀ he).mp hhi
  refine ⟨k, ?_, ?_⟩ <;> dsimp [k] <;> nlinarith

theorem exists_buffered_bin (M : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    {e : ℝ} (he : 0 < e)
    (hbound : ∀ j ≤ n, (51 / 100 : ℝ) ≤ M j ∧ M j ≤ 1)
    (hwidth : (49 / 100 : ℝ) ≤ n * e) :
    ∃ i < n, ∃ k : ℕ,
      let a : ℝ := 51 / 100 + e * k
      a ≤ 1 ∧ a ≤ M i ∧ M i < a + e ∧ M (i + 1) < a + 2 * e := by
  obtain ⟨i, hi, hstep⟩ := exists_small_increment M hn (e := e)
    (hbound 0 (Nat.zero_le _)).1 (hbound n le_rfl).2 (by linarith)
  obtain ⟨k, hklo, hkhi⟩ := exists_grid_rounding he (hbound i hi.le).1
  refine ⟨i, hi, k, ?_, hklo, hkhi, ?_⟩
  · exact hklo.trans (hbound i hi.le).2
  · linarith

theorem maximal_zero_of_floor_lt {ι : Type*} (L : ι → ℂ → ℂ)
    (zeros : Finset (ι × ℂ)) {floor M : ℝ}
    (hzero : ∀ p ∈ zeros, L p.1 p.2 = 0)
    (hmax : M ∈ insert floor (zeros.image (fun p => p.2.re)))
    (hfloor : floor < M) :
    ∃ χ ρ, (χ, ρ) ∈ zeros ∧ L χ ρ = 0 ∧ ρ.re = M := by
  classical
  rcases Finset.mem_insert.mp hmax with h | h
  · exact False.elim ((ne_of_gt hfloor) h)
  · obtain ⟨⟨χ, ρ⟩, hp, heq⟩ := Finset.mem_image.mp h
    exact ⟨χ, ρ, hp, hzero _ hp, heq⟩

theorem simultaneous_saturation {U δ r m ε A B : ℝ}
    (hU : 1 < U) (hδ : (1 / 50 : ℝ) ≤ δ) (hε : 0 ≤ ε)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hprod : U ^ (δ * (r + m) - ε) ≤ A * B)
    (hupperA : A ≤ U ^ (δ * r + ε))
    (hupperB : B ≤ U ^ (δ * min m (1 - m) + ε)) :
    m ≤ 1 / 2 + 75 * ε ∧
      U ^ (δ * r - 2 * ε) ≤ A ∧ U ^ (δ * m - 2 * ε) ≤ B := by
  have hU0 : 0 < U := by linarith
  have hδ0 : 0 ≤ δ := by linarith
  have hBcoarse : B ≤ U ^ (δ * m + ε) := by
    apply hupperB.trans
    exact Real.rpow_le_rpow_of_exponent_le hU.le
      (by have h := mul_le_mul_of_nonneg_left (min_le_left m (1 - m)) hδ0; linarith)
  have hpupper : A * B ≤ U ^ (δ * r + ε + (δ * min m (1 - m) + ε)) := by
    rw [Real.rpow_add hU0]
    exact mul_le_mul hupperA hupperB hB (Real.rpow_nonneg hU0.le _)
  have hexp := (Real.rpow_le_rpow_left_iff hU).mp (hprod.trans hpupper)
  have hlength : m ≤ 1 / 2 + 75 * ε := by
    by_cases hm : m ≤ 1 / 2
    · linarith
    · have hmin : min m (1 - m) = 1 - m := min_eq_right (by linarith)
      rw [hmin] at hexp
      have hm0 : 0 ≤ m - 1 / 2 := by linarith
      have hmul := mul_le_mul_of_nonneg_right hδ hm0
      nlinarith
  have hlowerA : U ^ (δ * r - 2 * ε) ≤ A := by
    have hp : U ^ (δ * r - 2 * ε) * U ^ (δ * m + ε) ≤
        A * U ^ (δ * m + ε) := by
      calc
        _ = U ^ (δ * (r + m) - ε) := by rw [← Real.rpow_add hU0]; congr 1; ring
        _ ≤ A * B := hprod
        _ ≤ _ := mul_le_mul_of_nonneg_left hBcoarse hA
    have hpos := Real.rpow_pos_of_pos hU0 (δ * m + ε)
    nlinarith
  have hlowerB : U ^ (δ * m - 2 * ε) ≤ B := by
    have hp : U ^ (δ * m - 2 * ε) * U ^ (δ * r + ε) ≤
        B * U ^ (δ * r + ε) := by
      calc
        _ = U ^ (δ * (r + m) - ε) := by rw [← Real.rpow_add hU0]; congr 1; ring
        _ ≤ A * B := hprod
        _ ≤ _ := by simpa [mul_comm] using mul_le_mul_of_nonneg_right hupperA hB
    have hpos := Real.rpow_pos_of_pos hU0 (δ * r + ε)
    nlinarith
  exact ⟨hlength, hlowerA, hlowerB⟩

theorem inverse_length_of_saturation {r m t ε κ : ℝ}
    (hsupport : t - κ ≤ r + m) (hplain : m ≤ 1 / 2 + 75 * ε) :
    t - 1 / 2 - 75 * ε - κ ≤ r := by linarith

theorem complex_simultaneous_saturation {U δ r m ε : ℝ} {M S : ℂ}
    (hU : 1 < U) (hδ : (1 / 50 : ℝ) ≤ δ) (hε : 0 ≤ ε)
    (hprod : U ^ (δ * (r + m) - ε) ≤ ‖M * S‖ ^ 2)
    (hupperM : ‖M‖ ^ 2 ≤ U ^ (δ * r + ε))
    (hupperS : ‖S‖ ^ 2 ≤ U ^ (δ * min m (1 - m) + ε)) :
    m ≤ 1 / 2 + 75 * ε ∧
      U ^ (δ * r - 2 * ε) ≤ ‖M‖ ^ 2 ∧
      U ^ (δ * m - 2 * ε) ≤ ‖S‖ ^ 2 := by
  apply simultaneous_saturation hU hδ hε (sq_nonneg _) (sq_nonneg _)
    _ hupperM hupperS
  simpa only [norm_mul, mul_pow] using hprod

end SevenEighths.Detector

end OAI

end Source701

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorZeros.lean; sha256: c976e6f433fd0963051eb31cd16607ac9c7d0d4f0fcb9810e173ee730a400727 -/
section Source702
namespace OAI

noncomputable section
open Set Filter
open scoped Classical Topology
namespace SevenEighths.HeckeDetectorZeros
open HeckeFamily

def rectangle (T : ℝ) : Set ℂ :=
  {s | (51/100 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T}

theorem rectangle_compact (T : ℝ) : IsCompact (rectangle T) := by
  have heq : rectangle T = Set.Icc (51/100 : ℝ) 1 ×ℂ Set.Icc (-T) T := by
    ext z
    simp only [rectangle, Set.mem_ofPred_eq, Complex.mem_reProdIm, Set.mem_Icc, abs_le]
    tauto
  rw [heq]
  exact isCompact_Icc.reProdIm isCompact_Icc

def zeros (χ : Character) (T : ℝ) : Set ℂ := {s ∈ rectangle T | LFunction χ s = 0}

theorem zeros_finite (χ : Character) (hχ : χ.residue ≠ 1) (T : ℝ) :
    (zeros χ T).Finite := by
  have ha : AnalyticOnNhd ℂ (LFunction χ) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (LFunction_entire_nonprincipal χ hχ)
  have hcod := ha.preimage_zero_mem_codiscreteWithin
    (LFunction_ne_zero_of_one_lt_re χ (by norm_num : 1 < (2 : ℂ).re))
    (Set.mem_univ (2 : ℂ)) isConnected_univ
  have hfin := (rectangle_compact T).finite_sdiff_of_mem_codiscreteWithin
    (codiscreteWithin_mono (Set.subset_univ (rectangle T)) hcod)
  convert hfin using 1
  ext s
  simp [zeros]

def zeroFinset (χ : Character) (hχ : χ.residue ≠ 1) (T : ℝ) : Finset ℂ :=
  (zeros_finite χ hχ T).toFinset

@[simp] theorem mem_zeroFinset (χ : Character) (hχ : χ.residue ≠ 1) (T : ℝ) (s : ℂ) :
    s ∈ zeroFinset χ hχ T ↔
      (51/100 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T ∧ LFunction χ s = 0 := by
  simp only [zeroFinset, Set.Finite.mem_toFinset, zeros, rectangle, Set.mem_ofPred_eq]
  tauto

variable {ι : Type*} [Fintype ι]

def familyZeros (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) :
    Finset (ι × ℂ) :=
  Finset.univ.biUnion (fun i => (zeroFinset (χ i) (hχ i) T).image (fun s => (i,s)))

@[simp] theorem mem_familyZeros (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1)
    (T : ℝ) (i : ι) (s : ℂ) :
    (i,s) ∈ familyZeros χ hχ T ↔
      (51/100 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T ∧ LFunction (χ i) s = 0 := by
  simp [familyZeros]

def realParts (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) : Finset ℝ :=
  insert (51/100) ((familyZeros χ hχ T).image (fun p => p.2.re))

theorem realParts_nonempty (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) :
    (realParts χ hχ T).Nonempty := Finset.insert_nonempty _ _

def zeroMaximum (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) : ℝ :=
  (realParts χ hχ T).max' (realParts_nonempty χ hχ T)

theorem zeroMaximum_mem (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) :
    zeroMaximum χ hχ T ∈ realParts χ hχ T := Finset.max'_mem _ _

theorem zeroMaximum_bounds (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) :
    (51/100 : ℝ) ≤ zeroMaximum χ hχ T ∧ zeroMaximum χ hχ T ≤ 1 := by
  constructor
  · exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  · apply Finset.max'_le
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · norm_num
    · obtain ⟨⟨i,s⟩, hs, rfl⟩ := Finset.mem_image.mp hx
      exact (mem_familyZeros χ hχ T i s |>.mp hs).2.1

theorem zero_re_le_maximum (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1)
    (T : ℝ) (i : ι) {s : ℂ} (hs : (51/100 : ℝ) ≤ s.re)
    (ht : |s.im| ≤ T) (hz : LFunction (χ i) s = 0) : s.re ≤ zeroMaximum χ hχ T := by
  have hle : s.re ≤ 1 := by
    by_contra hn
    exact LFunction_ne_zero_of_one_lt_re (χ i) (lt_of_not_ge hn) hz
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨(i,s), (mem_familyZeros χ hχ T i s).mpr ⟨hs, hle, ht, hz⟩, rfl⟩)

theorem maximum_attained (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ)
    (hmax : (51/100 : ℝ) < zeroMaximum χ hχ T) :
    ∃ i s, LFunction (χ i) s = 0 ∧ |s.im| ≤ T ∧ s.re = zeroMaximum χ hχ T := by
  have hm := zeroMaximum_mem χ hχ T
  rcases Finset.mem_insert.mp hm with hm | hm
  · exact False.elim ((ne_of_gt hmax) hm)
  · obtain ⟨⟨i,s⟩, hs, heq⟩ := Finset.mem_image.mp hm
    have hz := (mem_familyZeros χ hχ T i s).mp hs
    exact ⟨i,s,hz.2.2.2,hz.2.2.1,heq⟩

theorem zeroMaximum_mono (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1)
    {T T' : ℝ} (hT : T ≤ T') : zeroMaximum χ hχ T ≤ zeroMaximum χ hχ T' := by
  rcases lt_or_ge (51/100 : ℝ) (zeroMaximum χ hχ T) with hm | hm
  · obtain ⟨i,s,hz,ht,heq⟩ := maximum_attained χ hχ T hm
    rw [← heq]
    apply zero_re_le_maximum χ hχ T' i _ (ht.trans hT) hz
    rw [heq]
    exact hm.le
  · exact hm.trans (zeroMaximum_bounds χ hχ T').1

theorem nonzero_on_buffered_disk (χ : ι → Character) (hχ : ∀ j, (χ j).residue ≠ 1)
    (T a e : ℝ) (i : ℕ) (hT : 2 < T) (ha : (51/100 : ℝ) ≤ a) (he : 0 < e)
    (hmax : zeroMaximum χ hχ (3*(i+1 : ℕ)*T) < a+2*e)
    (j : ι) (t : ℝ) (ht : |t| ≤ (3*i+2 : ℕ)*T)
    {s : ℂ} (hs : s ∈ Metric.closedBall ((2 : ℂ)+t*Complex.I) (2-a-2*e)) :
    LFunction (χ j) s ≠ 0 := by
  have hn : ‖s-((2 : ℂ)+t*Complex.I)‖ ≤ 2-a-2*e := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hs
  have hr := Complex.abs_re_le_norm (s-((2 : ℂ)+t*Complex.I))
  have hi := Complex.abs_im_le_norm (s-((2 : ℂ)+t*Complex.I))
  norm_num at hr hi
  have hre : a+2*e ≤ s.re := by linarith [(abs_le.mp (hr.trans hn)).1]
  have him : |s.im| ≤ 3*(i+1 : ℕ)*T := by
    have ht' := abs_add_le (s.im-t) t
    rw [sub_add_cancel] at ht'
    push_cast at ht ⊢
    nlinarith [hi.trans hn]
  intro hz
  have hle := zero_re_le_maximum χ hχ (3*(i+1 : ℕ)*T) j (by linarith) him hz
  linarith

theorem exists_actual_buffered_bin (χ : ι → Character)
    (hχ : ∀ j, (χ j).residue ≠ 1) (T e : ℝ) (hT : 2 < T) (he : 0 < e)
    (n : ℕ) (hn : 0 < n) (hwidth : (49/100 : ℝ) ≤ n*e) :
    ∃ i k : ℕ, 1 ≤ i ∧ i ≤ n ∧
      let a : ℝ := 51/100+e*k
      a ≤ 1 ∧ a ≤ zeroMaximum χ hχ (3*i*T) ∧
      zeroMaximum χ hχ (3*i*T) < a+e ∧
      zeroMaximum χ hχ (3*(i+1 : ℕ)*T) < a+2*e ∧
      (51/100 < a → ∃ j s, LFunction (χ j) s = 0 ∧ a ≤ s.re ∧
        s.re < a+e ∧ |s.im| ≤ 3*i*T) ∧
      (∀ j t, |t| ≤ (3*i+2 : ℕ)*T → ∀ s ∈
        Metric.closedBall ((2 : ℂ)+t*Complex.I) (2-a-2*e), LFunction (χ j) s ≠ 0) := by
  let M : ℕ → ℝ := fun j => zeroMaximum χ hχ (3*(j+1 : ℕ)*T)
  obtain ⟨i,hk,k,hone,hlo,hhi,hnext⟩ := Detector.exists_buffered_bin M hn he
    (fun j _ => zeroMaximum_bounds χ hχ _) hwidth
  refine ⟨i+1,k,by omega,by omega,hone,hlo,hhi,?_,?_,?_⟩
  · exact hnext
  · intro ha
    obtain ⟨j,s,hz,ht,hs⟩ := maximum_attained χ hχ (3*(i+1 : ℕ)*T) (lt_of_lt_of_le ha hlo)
    exact ⟨j,s,hz,by rw [hs]; exact hlo,by rw [hs]; exact hhi,ht⟩
  · intro j t ht s hs
    apply nonzero_on_buffered_disk χ hχ T (51/100+e*k) e (i+1) hT
      (by nlinarith [Nat.cast_nonneg (α := ℝ) k]) he hnext j t ht hs

end SevenEighths.HeckeDetectorZeros

end

end OAI

end Source702

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DyadicControl.lean; sha256: 7b052b188a242174544251848e99ead459104f79134c9c9e0c36cdc684192f32 -/
section Source703
namespace OAI

noncomputable section
open scoped Classical Topology
open Set Metric
namespace SevenEighths.HeckeDyadicControl
open HeckeFamily HeckeLogarithmicInput HeckeLogarithmic HeckeFiniteDeletion
open HeckeDeletionBounds HeckeReciprocalGrowth

theorem original_disk_control (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (χ : Character), χ.residue ≠ 1 → ∀ a t : ℝ,
      1/2≤a → a≤1 →
      (∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), LFunction χ z ≠ 0) →
      ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-6*e),
        ‖LFunction χ z‖ + ‖HeckeReciprocal.reciprocal χ z‖ ≤
          C*(presentationComplexity χ t)^ε := by
  obtain ⟨Dp,B,hDp,_,hprimitive⟩ := HeckeLogarithmicActual.disk_control e ε he he' hε
  obtain ⟨Cd,hCd,hdelete⟩ := factors_radical_subpower_bound (1/2) ε (by norm_num) hε
  refine ⟨Dp*Cd,mul_pos hDp hCd,?_⟩
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
  have hbound := (hprimitive ψ hp a t ha ha' hzeroψ).1 z hz
  rw [hregular] at hbound
  have hz2 : z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e) :=
    closedBall_subset_ball (by linarith) hz
  have hzre : (1/2 : ℝ) ≤ z.re := by
    have hr := LogarithmicControl.disk_re_gt hz2
    linarith
  have hzpos : 0 < z.re := by linarith
  have hdel := hdelete χ.modulus ψ z hzre
  have hL : LFunction χ z = LFunction ψ z*factors χ.modulus ψ z :=
    LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hzpos
  have hR : HeckeReciprocal.reciprocal χ z =
      (LFunction ψ z)⁻¹*(factors χ.modulus ψ z)⁻¹ := by
    rw [HeckeDeletionReciprocal.reciprocal_eq_of_mask χ ψ hmask hzpos]
    simp only [HeckeReciprocal.reciprocal, ite_eq_right hψ]
  have hdel1 : ‖factors χ.modulus ψ z‖ ≤ Cd*((radical χ.modulus).absNorm : ℝ)^ε := by
    linarith [norm_nonneg ((factors χ.modulus ψ z)⁻¹)]
  have hdel2 : ‖(factors χ.modulus ψ z)⁻¹‖ ≤ Cd*((radical χ.modulus).absNorm : ℝ)^ε := by
    linarith [norm_nonneg (factors χ.modulus ψ z)]
  have hQ : complexity ψ t ≤ complexity χ t := by
    unfold complexity
    have hn' : (ψ.modulus.absNorm : ℝ) ≤ χ.modulus.absNorm := by exact_mod_cast hn
    gcongr
  have hc0 : 0 ≤ complexity ψ t := (Real.exp_pos 1).le.trans (complexity_ge_exp ψ t)
  have hr0 : 0 ≤ ((radical χ.modulus).absNorm : ℝ) := by positivity
  rw [hL,hR,norm_mul,norm_mul]
  calc
    _ ≤ (‖LFunction ψ z‖+‖(LFunction ψ z)⁻¹‖)*
        (Cd*((radical χ.modulus).absNorm : ℝ)^ε) := by
      have h1 := mul_le_mul_of_nonneg_left hdel1 (norm_nonneg (LFunction ψ z))
      have h2 := mul_le_mul_of_nonneg_left hdel2 (norm_nonneg ((LFunction ψ z)⁻¹))
      nlinarith
    _ ≤ (Dp*(complexity ψ t)^ε)*(Cd*((radical χ.modulus).absNorm : ℝ)^ε) :=
      mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = (Dp*Cd)*(((radical χ.modulus).absNorm : ℝ)*complexity ψ t)^ε := by
      rw [Real.mul_rpow hr0 hc0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg hr0 hc0) (mul_le_mul_of_nonneg_left hQ hr0) hε.le)
      (mul_pos hDp hCd).le

theorem buffered_original_control (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue ≠ 1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T) < a+2*e →
      ∀ (j : ι) (t : ℝ), |t| ≤ (3*i+2 : ℕ)*T →
      ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-6*e),
        ‖LFunction (χ j) z‖+‖HeckeReciprocal.reciprocal (χ j) z‖ ≤
          C*(presentationComplexity (χ j) t)^ε := by
  obtain ⟨C,hC,hbound⟩ := original_disk_control e ε he he' hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j t ht z hz
  exact hbound (χ j) (hχ j) a t (by linarith) ha'
    (fun w hw => HeckeDetectorZeros.nonzero_on_buffered_disk χ hχ T a e i hT ha he
      hmax j t ht (ball_subset_closedBall hw)) z hz

end SevenEighths.HeckeDyadicControl

end

end OAI

end Source703

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DyadicEstimates.lean; sha256: f77d6813d5a8b8e1a8ffe38ef5c8aab47a3e549879a34b10a26fe1935e0b0139 -/
section Source704
namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem rapid_tail_bound (F : ℝ → ℂ) (C T : ℝ) (n : ℕ) (hC : 0≤C) (hT : 0≤T)
    (hF : ∀ t : ℝ, (1+|t|)^(n+2)*‖F t‖≤C) :
    ‖∫ t : ℝ in (Icc (-T) T)ᶜ, F t‖ ≤ C/(1+T)^n*Real.pi := by
  have hen (t : ℝ) (ht : t ∈ (Icc (-T) T)ᶜ) :
      ‖F t‖≤(C/(1+T)^n)*(1+t^2)⁻¹ := by
    have ht' : T≤|t| := by
      by_contra h
      have hab : |t|<T := lt_of_not_ge h
      exact ht ⟨(abs_lt.mp hab).1.le, (abs_lt.mp hab).2.le⟩
    have hp : (1+T)^n*(1+t^2)≤(1+|t|)^(n+2) := by
      rw [pow_add]
      apply mul_le_mul
      · exact pow_le_pow_left₀ (by linarith) (by linarith) n
      · nlinarith [sq_abs t, abs_nonneg t]
      · positivity
      · positivity
    have hh : ‖F t‖*((1+T)^n*(1+t^2))≤C :=
      (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans (by simpa [mul_comm] using hF t)
    have hb := (le_div_iff₀ (by positivity : 0<(1+T)^n*(1+t^2))).mpr hh
    simpa [div_mul_eq_div_div, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hb
  have hint := (integrable_inv_one_add_sq.const_mul (C/(1+T)^n))
  calc
    _ ≤ ∫ t : ℝ in (Icc (-T) T)ᶜ, (C/(1+T)^n)*(1+t^2)⁻¹ := by
      apply norm_integral_le_of_norm_le hint.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht
      exact hen t ht
    _ ≤ ∫ t : ℝ, (C/(1+T)^n)*(1+t^2)⁻¹ :=
      integral_mono_measure Measure.restrict_le_self (by filter_upwards [] with t; positivity) hint
    _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

theorem absolute_tail_bound (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D r σ freq C T : ℝ) (n : ℕ) (hD : 0<D) (hr : 1<r+σ) (hC : 0≤C) (hT : 0≤T)
    (hm : ∀ t : ℝ, (1+|t|)^(n+2)*‖mellin W ((r : ℂ)+t*I)‖≤C) :
    ‖∫ t : ℝ in (Icc (-T) T)ᶜ, integrand χ inverse W D σ freq ((r : ℂ)+t*I)‖ ≤
      (C*D^(r+σ-1/2)*HeckeReciprocalBound.bound (r+σ))/(1+T)^n*Real.pi := by
  apply rapid_tail_bound _ _ T n
  · exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hD.le _))
      (tsum_nonneg (fun _ => norm_nonneg _))
  · exact hT
  · intro t
    rw [integrand_norm χ inverse W D σ freq hD]
    have hb := series_norm_le χ inverse hr (s := (r : ℂ)+t*I+shift σ freq) (by simp)
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
      sub_self, add_zero]
    calc
      _ = ((1+|t|)^(n+2)*‖mellin W ((r : ℂ)+t*I)‖)*D^(r+σ-1/2)*
        ‖series χ inverse ((r : ℂ)+t*I+shift σ freq)‖ := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right (hm t) (Real.rpow_nonneg hD.le _))
        hb (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg hD.le _))

theorem central_segment_bound (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D l σ freq C K T : ℝ) (hD : 0<D) (hC : 0≤C) (hK : 0≤K) (hT : 0≤T)
    (hm : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤C)
    (hs : ∀ t ∈ Icc (-T) T, ‖series χ inverse ((l : ℂ)+t*I+shift σ freq)‖≤K) :
    ‖∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((l : ℂ)+t*I)‖ ≤
      C*D^(l+σ-1/2)*K*Real.pi := by
  rw [intervalIntegral.integral_of_le (by linarith : -T≤T)]
  have hint := integrable_inv_one_add_sq.const_mul (C*D^(l+σ-1/2)*K)
  calc
    _ ≤ ∫ t : ℝ in Ioc (-T) T, (C*D^(l+σ-1/2)*K)*(1+t^2)⁻¹ := by
      apply norm_integral_le_of_norm_le hint.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [integrand_norm χ inverse W D σ freq hD]
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

end SevenEighths.HeckeDyadic

end

end OAI

end Source704

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DyadicJoins.lean; sha256: d599abac4adc5bdc2a06338be16ad57f3be6197273b572c1e649941779878c15 -/
section Source705
namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem horizontal_join_bound (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq l r y C K : ℝ) (n : ℕ)
    (hD : 1≤D) (hlr : l≤r) (hC : 0≤C) (_hK : 0≤K)
    (hm : ∀ x ∈ Icc l r, (1+|y|)^n*‖mellin W ((x : ℂ)+y*I)‖≤C)
    (hs : ∀ x ∈ Icc l r, ‖series χ inverse ((x : ℂ)+y*I+shift σ freq)‖≤K) :
    ‖∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+y*I)‖ ≤
      (C*D^(r+σ-1/2)*K/(1+|y|)^n)*|r-l| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  have hx' : x ∈ Icc l r := by simpa [uIcc_of_le hlr] using uIoc_subset_uIcc hx
  have hb : ‖mellin W ((x : ℂ)+y*I)‖≤C/(1+|y|)^n := by
    apply (le_div_iff₀ (by positivity : 0<(1+|y|)^n)).mpr
    simpa [mul_comm] using hm x hx'
  have hpow : D^(x+σ-1/2)≤D^(r+σ-1/2) :=
    Real.rpow_le_rpow_of_exponent_le hD (by linarith [hx'.2])
  rw [integrand_norm χ inverse W D σ freq (by linarith)]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
    sub_self, add_zero]
  calc
    _ ≤ (C/(1+|y|)^n)*D^(r+σ-1/2)*K :=
      mul_le_mul (mul_le_mul hb hpow (by positivity) (by positivity))
        (hs x hx') (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem profile_strip_decay (a b : ℝ) (ha : 0<a) (l r : ℝ) (n : ℕ) :
    ∃ (S : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ)⊆Icc a b →
      ∀ x ∈ Icc l r, ∀ y : ℝ,
      (1+|y|)^n*‖mellin W ((x : ℂ)+y*I)‖≤
        C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
  CubicReflectionKernel.mellin_strip_source_bound a b ha l r n

end SevenEighths.HeckeDyadic

end

end OAI

end Source705

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DyadicBuffered.lean; sha256: 508090ebf0750c0910207745e020c6de3f258598c5fb66529798cb288cb38672 -/
section Source706
namespace OAI

noncomputable section
open scoped Classical Topology
open Set Metric Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeLogarithmic HeckeReciprocalGrowth

theorem presentationComplexity_mono_height (χ : Character) {t H : ℝ}
    (ht : |t|≤H) : presentationComplexity χ t≤presentationComplexity χ H := by
  unfold presentationComplexity complexity
  have hH : 0≤H := (abs_nonneg t).trans ht
  rw [abs_of_nonneg hH]
  gcongr

theorem buffered_rectangle_control (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (z : ℂ), a+6*e≤z.re → z.re≤2 →
      |z.im|≤(3*i+2 : ℕ)*T →
      LFunction (χ j) z≠0 ∧
      ‖LFunction (χ j) z‖+‖HeckeReciprocal.reciprocal (χ j) z‖≤
        C*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε := by
  obtain ⟨C,hC,hbound⟩ := HeckeDyadicControl.buffered_original_control e ε he he' hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j z hzl hzr hzi
  have hz6 : z ∈ closedBall ((2 : ℂ)+z.im*I) (2-a-6*e) := by
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
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow
  · unfold presentationComplexity complexity
    positivity
  · exact presentationComplexity_mono_height _ hzi
  · exact hε.le

theorem translated_rectangle_mem {a e σ freq l r H T : ℝ}
    (hl : a+6*e≤l+σ) (hr : r+σ≤2) (hlr : l≤r) (hT : 0≤T)
    (hfreq : |freq|+T≤H) {s : ℂ} (hs : s ∈ (uIcc l r ×ℂ uIcc (-T) T)) :
    a+6*e≤(s+shift σ freq).re ∧ (s+shift σ freq).re≤2 ∧
      |(s+shift σ freq).im|≤H := by
  have hs' : s.re ∈ Icc l r ∧ s.im ∈ Icc (-T) T := by
    change s.re ∈ uIcc l r ∧ s.im ∈ uIcc (-T) T at hs
    simpa [uIcc_of_le hlr,uIcc_of_le (by linarith : -T≤T)] using hs
  have hsi : |s.im|≤T := abs_le.mpr hs'.2
  constructor
  · simp only [add_re,shift_re]
    linarith [hs'.1.1]
  constructor
  · simp only [add_re,shift_re]
    linarith [hs'.1.2]
  · have hi : (s+shift σ freq).im=s.im-freq := by simp [shift,sub_eq_add_neg]
    rw [hi]
    exact (abs_sub _ _).trans (by linarith)

end SevenEighths.HeckeDyadic

end

end OAI

end Source706

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DyadicPointwise.lean; sha256: c59a840dc3c2a74b862306eb443e5d9cfff4a62d58139890684a27922f34ec22 -/
section Source707
namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set MeasureTheory Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem norm_four_sides (A B C D : ℂ) :
    ‖A+I*(B-C)+D‖≤‖A‖+‖B‖+‖C‖+‖D‖ := by
  have h₁ := norm_add_le (A+I*(B-C)) D
  have h₂ := norm_add_le A (I*(B-C))
  have h₃ := norm_sub_le B C
  simp only [norm_mul,norm_I,one_mul] at h₂
  linarith

theorem polynomial_bound_of_rectangle (χ : Character) (hχ : χ.residue≠1)
    (inverse : Bool) (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T C₂ Cn K : ℝ) (n : ℕ)
    (hD : 1≤D) (hlr : l≤r) (hr : 1<r+σ) (hT : 0≤T)
    (hC₂ : 0≤C₂) (hCn : 0≤Cn) (hK : 0≤K)
    (hm₂ : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤C₂)
    (hmn : ∀ x ∈ Icc l r, ∀ t : ℝ,
      (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), inverse=true →
      LFunction χ (s+shift σ freq)≠0)
    (hs : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T),
      ‖series χ inverse (s+shift σ freq)‖≤K) :
    ‖polynomial χ inverse W D σ freq‖≤(1/(2*Real.pi))*
      (C₂*D^(l+σ-1/2)*K*Real.pi +
       2*(Cn*D^(r+σ-1/2)*K/(1+T)^n)*|r-l| +
       (Cn*D^(r+σ-1/2)*HeckeReciprocalBound.bound (r+σ))/(1+T)^n*Real.pi) := by
  have hDp : 0<D := by linarith
  have hmem (x t : ℝ) (hx : x∈Icc l r) (ht : t∈Icc (-T) T) :
      ((x : ℂ)+t*I) ∈ (uIcc l r ×ℂ uIcc (-T) T) := by
    change (((x : ℂ)+t*I).re∈uIcc l r) ∧ (((x : ℂ)+t*I).im∈uIcc (-T) T)
    simpa [uIcc_of_le hlr,uIcc_of_le (by linarith : -T≤T)] using And.intro hx ht
  have hcentral := central_segment_bound χ inverse W D l σ freq C₂ K T hDp hC₂ hK hT
    hm₂ (fun t ht => hs _ (hmem l t ⟨le_rfl,hlr⟩ ht))
  have hm (x : ℝ) (hx : x∈Icc l r) (t : ℝ) :
      (1+|t|)^n*‖mellin W ((x : ℂ)+t*I)‖≤Cn := by
    apply le_trans _ (hmn x hx t)
    gcongr
    · exact le_add_of_nonneg_right (abs_nonneg t)
    · omega
  have hbottom := horizontal_join_bound χ inverse W D σ freq l r (-T) Cn K n hD hlr hCn hK
    (fun x hx => hm x hx (-T)) (fun x hx => hs _ (hmem x (-T) hx ⟨le_rfl,by linarith⟩))
  have htop := horizontal_join_bound χ inverse W D σ freq l r T Cn K n hD hlr hCn hK
    (fun x hx => hm x hx T) (fun x hx => hs _ (hmem x T hx ⟨by linarith,le_rfl⟩))
  simp only [abs_neg,abs_of_nonneg hT,ofReal_neg] at hbottom htop
  have htail := absolute_tail_bound χ inverse W D r σ freq Cn T n hDp hr hCn hT
    (hmn r ⟨hlr,le_rfl⟩)
  rw [polynomial_finite_shift χ hχ inverse W a b ha hWs hW D σ freq l r T hDp hr hT hz,
    norm_mul]
  have hnorm : ‖(1/(2*Real.pi) : ℂ)‖=(1/(2*Real.pi) : ℝ) := by
    simp [Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_four_sides _ _ _ _).trans (by linarith)

theorem polynomial_bound_of_rectangle_split (χ : Character) (hχ : χ.residue≠1)
    (inverse : Bool) (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T C₂ Cn K Kc : ℝ) (n : ℕ)
    (hD : 1≤D) (hlr : l≤r) (hr : 1<r+σ) (hT : 0≤T)
    (hC₂ : 0≤C₂) (hCn : 0≤Cn) (hK : 0≤K) (hKc : 0≤Kc)
    (hm₂ : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤C₂)
    (hmn : ∀ x ∈ Icc l r, ∀ t : ℝ,
      (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn)
    (hcentralSeries : ∀ t ∈ Icc (-T) T, ‖series χ inverse ((l : ℂ)+t*I+shift σ freq)‖≤Kc)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), inverse=true →
      LFunction χ (s+shift σ freq)≠0)
    (hs : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T),
      ‖series χ inverse (s+shift σ freq)‖≤K) :
    ‖polynomial χ inverse W D σ freq‖≤(1/(2*Real.pi))*
      (C₂*D^(l+σ-1/2)*Kc*Real.pi +
       2*(Cn*D^(r+σ-1/2)*K/(1+T)^n)*|r-l| +
       (Cn*D^(r+σ-1/2)*HeckeReciprocalBound.bound (r+σ))/(1+T)^n*Real.pi) := by
  have hDp : 0<D := by linarith
  have hmem (x t : ℝ) (hx : x∈Icc l r) (ht : t∈Icc (-T) T) :
      ((x : ℂ)+t*I) ∈ (uIcc l r ×ℂ uIcc (-T) T) := by
    change (((x : ℂ)+t*I).re∈uIcc l r) ∧ (((x : ℂ)+t*I).im∈uIcc (-T) T)
    simpa [uIcc_of_le hlr,uIcc_of_le (by linarith : -T≤T)] using And.intro hx ht
  have hcentral := central_segment_bound χ inverse W D l σ freq C₂ Kc T hDp hC₂ hKc hT
    hm₂ hcentralSeries
  have hm (x : ℝ) (hx : x∈Icc l r) (t : ℝ) :
      (1+|t|)^n*‖mellin W ((x : ℂ)+t*I)‖≤Cn := by
    apply le_trans _ (hmn x hx t)
    gcongr
    · exact le_add_of_nonneg_right (abs_nonneg t)
    · omega
  have hbottom := horizontal_join_bound χ inverse W D σ freq l r (-T) Cn K n hD hlr hCn hK
    (fun x hx => hm x hx (-T)) (fun x hx => hs _ (hmem x (-T) hx ⟨le_rfl,by linarith⟩))
  have htop := horizontal_join_bound χ inverse W D σ freq l r T Cn K n hD hlr hCn hK
    (fun x hx => hm x hx T) (fun x hx => hs _ (hmem x T hx ⟨by linarith,le_rfl⟩))
  simp only [abs_neg,abs_of_nonneg hT,ofReal_neg] at hbottom htop
  have htail := absolute_tail_bound χ inverse W D r σ freq Cn T n hDp hr hCn hT
    (hmn r ⟨hlr,le_rfl⟩)
  rw [polynomial_finite_shift χ hχ inverse W a b ha hWs hW D σ freq l r T hDp hr hT hz,
    norm_mul]
  have hnorm : ‖(1/(2*Real.pi) : ℂ)‖=(1/(2*Real.pi) : ℝ) := by
    simp [Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_four_sides _ _ _ _).trans (by linarith)

end SevenEighths.HeckeDyadic

end

end OAI

end Source707

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DyadicBounded.lean; sha256: 737524365d6749c9238a946557df14270b4dd36eecbd58a0608a9c560fd2dcc6 -/
section Source708
namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeReciprocalGrowth

theorem buffered_polynomial_bound (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (inverse : Bool) (W : ℝ → ℂ) (A B : ℝ),
      0<A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ (D σ freq V C₂ Cn : ℝ) (n : ℕ), 1≤D → 0≤V →
      |freq|+V≤(3*i+2 : ℕ)*T → 0≤C₂ → 0≤Cn →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((a+6*e-σ : ℝ) : ℂ)+t*I)‖≤C₂) →
      (∀ x ∈ Icc (a+6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn) →
      let K := C*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε
      ‖polynomial (χ j) inverse W D σ freq‖≤(1/(2*Real.pi))*
        (C₂*D^(a+6*e-1/2)*K*Real.pi +
         2*(Cn*D^(3/2 : ℝ)*K/(1+V)^n)*|2-a-6*e| +
         (Cn*D^(3/2 : ℝ)*HeckeReciprocalBound.bound 2)/(1+V)^n*Real.pi) := by
  obtain ⟨C,hC,hrect⟩ := buffered_rectangle_control e ε he he' hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j inverse W A B hA hWs hW
    D σ freq V C₂ Cn n hD hV hfreq hC₂ hCn hm₂ hmn
  dsimp only
  let K := C*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε
  have hK : 0≤K := mul_nonneg hC.le (Real.rpow_nonneg (by
    unfold presentationComplexity HeckeLogarithmic.complexity
    positivity) _)
  have hlr : a+6*e-σ≤2-σ := by linarith
  have hmem {s : ℂ} (hs : s ∈ (uIcc (a+6*e-σ) (2-σ) ×ℂ uIcc (-V) V)) :=
    translated_rectangle_mem (a:=a) (e:=e) (σ:=σ) (freq:=freq)
      (by linarith : a+6*e≤a+6*e-σ+σ) (by linarith : 2-σ+σ≤2) hlr hV hfreq hs
  have hz {s : ℂ} (hs : s ∈ (uIcc (a+6*e-σ) (2-σ) ×ℂ uIcc (-V) V)) :=
    hrect χ hχ T a i hT ha ha' hmax j (s+shift σ freq) (hmem hs).1 (hmem hs).2.1 (hmem hs).2.2
  have hseries (s : ℂ) (hs : s ∈ (uIcc (a+6*e-σ) (2-σ) ×ℂ uIcc (-V) V)) :
      ‖series (χ j) inverse (s+shift σ freq)‖≤K := by
    have hb := (hz hs).2
    cases inverse
    · exact (le_add_of_nonneg_right (norm_nonneg _)).trans hb
    · exact (le_add_of_nonneg_left (norm_nonneg _)).trans hb
  have hbound := polynomial_bound_of_rectangle (χ j) (hχ j) inverse W A B hA hWs hW
    D σ freq (a+6*e-σ) (2-σ) V C₂ Cn K n hD hlr (by linarith) hV hC₂ hCn hK hm₂ hmn
    (fun _ hs _ => (hz hs).1) hseries
  dsimp only [K] at hbound
  convert hbound using 1 ; congr 2 <;> ring_nf

end SevenEighths.HeckeDyadic

end

end OAI

end Source708

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DyadicReflection.lean; sha256: 8932f905bd7b3fb05b915fa08e8aea2e42289e82298b8246b1a9ed81df78a188 -/
section Source709
namespace OAI

noncomputable section
open scoped Classical Topology
open Set Complex
namespace SevenEighths.HeckeDyadicReflection
open HeckeFamily HeckePrimitive HeckeStripActual

variable (c : O) [NeZero c]

theorem functional_equation (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O))=1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ≠1)
    {s : ℂ} (hs : s.re<1) :
    LFunction (character c χ hu) s = TraceCharacter.normalizedGauss c χ *
      (HeckeStrip.completionScale (conductor c) : ℂ)^(1-2*s) *
      (Complex.Gamma (1-s)/Complex.Gamma s) *
      LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (1-s) := by
  by_cases h0 : s=0
  · subst s
    rw [LFunction_eq_uncompleted c χ hu hp hχ]
    simp
  have h1 : s≠1 := by intro h; norm_num [h] at hs
  have hs0 : 1-s≠0 := sub_ne_zero.mpr (Ne.symm h1)
  have hs1 : 1-s≠1 := by intro h; apply h0; linear_combination -h
  have hΓ : Complex.Gamma (1-s)≠0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have he := completedL_functional_equation c χ hu hp hs0 hs1
  rw [sub_sub_cancel] at he
  rw [LFunction_eq_uncompleted c χ hu hp hχ,he,
    completedL_eq_standard c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv hs0 hs1 hΓ]
  have ha : ((HeckeStrip.completionScale (conductor c)) : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (HeckeStrip.completionScale_pos _
      (lt_of_lt_of_le zero_lt_one (conductor_ge_one c))).ne'
  have hpow : (HeckeStrip.completionScale (conductor c) : ℂ)^(-s)*
      (HeckeStrip.completionScale (conductor c) : ℂ)^(1-s)=
      (HeckeStrip.completionScale (conductor c) : ℂ)^(1-2*s) := by
    rw [←Complex.cpow_add _ _ ha]
    congr 1
    ring
  rw [div_eq_mul_inv]
  calc
    _ = TraceCharacter.normalizedGauss c χ *
        ((HeckeStrip.completionScale (conductor c) : ℂ)^(-s)*
          (HeckeStrip.completionScale (conductor c) : ℂ)^(1-s)) *
        (Complex.Gamma (1-s)*(Complex.Gamma s)⁻¹) *
        LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (1-s) := by ring
    _ = _ := by rw [hpow]

theorem gamma_real_ratio_bound : ∃ C : ℝ, 0<C ∧
    ∀ x ∈ Icc (-(1/10 : ℝ)) (1/2), Real.Gamma (1-x)/Real.Gamma (x+2)≤C := by
  have hcont : ContinuousOn (fun x : ℝ => Real.Gamma (1-x)/Real.Gamma (x+2))
      (Icc (-(1/10 : ℝ)) (1/2)) := by
    intro x hx
    have hnum : DifferentiableAt ℝ Real.Gamma (1-x) :=
      Real.differentiableAt_Gamma (by intro n hn; have hnn := Nat.cast_nonneg (α:=ℝ) n; linarith [hx.2])
    have hden : DifferentiableAt ℝ Real.Gamma (x+2) :=
      Real.differentiableAt_Gamma (by intro n hn; have hnn := Nat.cast_nonneg (α:=ℝ) n; linarith [hx.1])
    exact ((hnum.continuousAt.comp (g := Real.Gamma) (f := fun y : ℝ => 1-y) (show ContinuousAt (fun y : ℝ => 1-y) x by fun_prop)).div
      (hden.continuousAt.comp (g := Real.Gamma) (f := fun y : ℝ => y+2) (show ContinuousAt (fun y : ℝ => y+2) x by fun_prop))
      (Real.Gamma_pos_of_pos (show 0<x+2 by linarith [hx.1])).ne').continuousWithinAt
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨|C|+1,by positivity,?_⟩
  intro x hx
  exact (le_abs_self _).trans ((hC x hx).trans (by linarith [le_abs_self C]))

theorem gamma_ratio_strip_bound : ∃ C : ℝ, 0<C ∧ ∀ s : ℂ,
    -(1/10 : ℝ)≤s.re → s.re≤1/2 →
    ‖Complex.Gamma (1-s)/Complex.Gamma s‖≤C*(3+|s.im|)^2 := by
  obtain ⟨C,hC,hreal⟩ := gamma_real_ratio_bound
  refine ⟨C,hC,?_⟩
  intro s hl hr
  have hb := CubicReflectionKernel.Gamma_shifted_pair_bound
    (1/2) (1/2-s.re) (-s.im) 2 (by linarith) (by norm_num; linarith)
  have hnum : ((1/2 : ℝ) : ℂ)+((1/2-s.re : ℝ)+(-s.im)*I)=1-s := by
    apply Complex.ext <;> simp; ring
  have hden : ((1/2 : ℝ) : ℂ)-((1/2-s.re : ℝ)+(-s.im)*I)+(2 : ℕ)=s+2 := by
    apply Complex.ext <;> simp
  simp only [ofReal_neg] at hb
  rw [hnum,hden] at hb
  have hreal' := hreal s.re ⟨hl,hr⟩
  have hb' : ‖Complex.Gamma (1-s)/Complex.Gamma (s+2)‖≤C := by
    apply hb.trans
    convert hreal' using 1; congr 1 <;> ring_nf
  have heq : Complex.Gamma (1-s)/Complex.Gamma s =
      (∏ k ∈ Finset.range 2, (s+k))*(Complex.Gamma (1-s)/Complex.Gamma (s+2)) := by
    rw [div_eq_mul_inv,CubicReflectionKernel.inverse_Gamma_shift s 2]
    simp only [Nat.cast_ofNat,div_eq_mul_inv]
    ring
  have hs : ‖s‖≤1+|s.im| := by
    have hsr : |s.re|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
    have hn := Complex.norm_le_abs_re_add_abs_im s
    linarith
  have hf := CubicReflectionKernel.norm_Gamma_shift_factor s 2
  norm_num only [Nat.cast_ofNat] at hf
  have hf' : ‖∏ k ∈ Finset.range 2,(s+k)‖≤(3+|s.im|)^2 :=
    hf.trans (pow_le_pow_left₀ (by positivity) (show ‖s‖+2≤3+|s.im| by linarith) 2)
  rw [heq,norm_mul]
  exact (mul_le_mul hf' hb' (norm_nonneg _) (sq_nonneg _)).trans_eq (mul_comm _ _)

theorem completionScale_rpow_le {Q x : ℝ} (hQ : 0<Q) (hx : 0≤x) :
    HeckeStrip.completionScale Q ^ x≤Q^(x/2) := by
  have hs3 : Real.sqrt 3≤2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  have hscale : HeckeStrip.completionScale Q≤Real.sqrt Q := by
    unfold HeckeStrip.completionScale
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ)≤3)]
    apply (div_le_iff₀ (by positivity : 0<2*Real.pi)).mpr
    nlinarith [Real.sqrt_nonneg Q,Real.pi_gt_three]
  calc
    _ ≤ (Real.sqrt Q)^x := Real.rpow_le_rpow
      (HeckeStrip.completionScale_pos Q hQ).le hscale hx
    _ = _ := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_mul hQ.le]
      congr 1
      ring

theorem primitive_reflected_bound : ∃ C : ℝ, 0<C ∧
    ∀ (c : O) [NeZero c] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O))=1)
      (_hp : FiniteFourier.IsPrimitiveOnIdeals χ), χ≠1 →
    ∀ s : ℂ, -(1/10 : ℝ)≤s.re → s.re≤1/2 →
    ‖LFunction (character c χ hu) s‖≤
      C*(conductor c)^(1/2-s.re)*(3+|s.im|)^2*
        ‖LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (1-s)‖ := by
  obtain ⟨C,hC,hgamma⟩ := gamma_ratio_strip_bound
  refine ⟨C,hC,?_⟩
  intro c _ χ hu hp hχ s hl hr
  rw [functional_equation c χ hu hp hχ (by linarith),norm_mul,norm_mul,norm_mul,
    TraceCharacter.normalizedGauss_norm c χ hp,one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (HeckeStrip.completionScale_pos _
      (lt_of_lt_of_le zero_lt_one (conductor_ge_one c)))]
  have hscale := completionScale_rpow_le
    (lt_of_lt_of_le zero_lt_one (conductor_ge_one c)) (show 0≤1-2*s.re by linarith)
  have he : (1-2*s).re=1-2*s.re := by simp
  rw [he]
  have he' : (1-2*s.re)/2=1/2-s.re := by ring
  rw [he'] at hscale
  calc
    _ ≤ ((conductor c)^(1/2-s.re)*(C*(3+|s.im|)^2))*
        ‖LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (1-s)‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul hscale (hgamma s hl hr)
        (norm_nonneg _) (Real.rpow_nonneg (by exact_mod_cast (conductor_ge_one c).trans' zero_le_one) _))
        (norm_nonneg _)
    _ = _ := by ring

end SevenEighths.HeckeDyadicReflection

end

end OAI

end Source709

/- Original source: OAI/NumberTheory/DirichletL/Hecke/Conjugation.lean; sha256: 2350c2d8eb7ee17af11ac6d3ee52fd57ac4e48e3a97ae16058041a95b70c8278 -/
section Source710
namespace OAI

noncomputable section
open scoped Classical Topology ComplexConjugate
open Complex
namespace SevenEighths.HeckeFamily

theorem idealCoeff_inverse_conj (χ : Character) (J : Ideal O) :
    idealCoeff χ.inverse J=conj (idealCoeff χ J) := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  by_cases hJ : J=0
  · subst J
    rw [map_zero,map_zero,map_zero]
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero J hJ
  rw [←ConcretePrimeRowBridge.span_idealGenerator J,
    idealCoeff_span χ.inverse hg,idealCoeff_span χ hg]
  exact (MulChar.star_apply' χ.residue _).symm

theorem idealTerm_inverse_conj (χ : Character) (s : ℂ) (J : Ideal O) :
    idealTerm χ.inverse s J=conj (idealTerm χ (conj s) J) := by
  by_cases hJ : J=0
  · subst J
    simp only [idealTerm,map_zero,zero_div]
  have hN : (0 : ℝ)<J.absNorm := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hpow := Complex.cpow_conj ((J.absNorm : ℝ) : ℂ) (conj s)
    (by rw [Complex.arg_ofReal_of_nonneg hN.le]; exact Real.pi_ne_zero.symm)
  simp only [conj_ofReal, conj_conj] at hpow
  unfold idealTerm
  rw [idealCoeff_inverse_conj,map_div₀]
  congr 1

theorem LFunction_inverse_conj (χ : Character) (hχ : χ.residue≠1) (s : ℂ) :
    LFunction χ.inverse s=conj (LFunction χ (conj s)) := by
  have hi : χ.inverse.residue≠1 := by
    change χ.residue⁻¹≠1
    simpa only [ne_eq,inv_eq_one] using hχ
  have hA := LFunction_entire_nonprincipal χ.inverse hi
  have hB : Differentiable ℂ (fun z => conj (LFunction χ (conj z))) := by
    intro z
    simpa only [Function.comp_def,conj_conj] using
      (LFunction_entire_nonprincipal χ hχ (conj z)).conj_conj
  have he : LFunction χ.inverse=(fun z => conj (LFunction χ (conj z))) := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr hA).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hB) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ)<(2 : ℂ).re)] with z hz
    rw [LFunction_eq_ideal_tsum χ.inverse hz,LFunction_eq_ideal_tsum χ (by simpa using hz),conj_tsum]
    exact tsum_congr (idealTerm_inverse_conj χ z)
  exact congr_fun he s

end SevenEighths.HeckeFamily

end

end OAI

end Source710

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DyadicReflectedFamily.lean; sha256: e65009fce75c354379fe7d939628b5d7e8744d39112d2f939a13b7ebbfc6f15f -/
section Source711
namespace OAI

noncomputable section
open scoped Classical Topology ComplexConjugate
open Complex Set
namespace SevenEighths.HeckeDyadicReflection
open HeckeFamily HeckePresentation HeckeFiniteDeletion

theorem family_reflected_bound : ∃ C : ℝ, 0<C ∧ ∀ η : Character,
    FiniteFourier.IsPrimitiveOnIdeals η.residue → η.residue≠1 →
    ∀ s : ℂ, -(1/10 : ℝ)≤s.re → s.re≤1/2 →
    ‖LFunction η s‖≤C*(η.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
      ‖LFunction η (1-conj s)‖ := by
  obtain ⟨C,hC,hbound⟩ := primitive_reflected_bound
  refine ⟨C,hC,?_⟩
  intro η hp hη s hl hr
  have h := hbound (generator η) (principalResidue η) (principalResidue_unit η)
    (principalResidue_primitive η hp) (principalResidue_ne_one η hη) s hl hr
  have hi : HeckePrimitive.character (generator η) (principalResidue η)⁻¹
      (HeckePrimitive.inverse_unit_trivial (generator η) (principalResidue η) (principalResidue_unit η)) =
      (principalCharacter η).inverse := rfl
  rw [hi,LFunction_inverse_conj (principalCharacter η) (principalResidue_ne_one η hη),
    norm_conj,map_sub,map_one] at h
  change ‖LFunction (principalCharacter η) s‖≤_ at h
  rw [LFunction_principalCharacter η hη,LFunction_principalCharacter η hη] at h
  simpa only [HeckeStripActual.conductor,span_generator] using h

theorem LFunction_eq_of_mask_entire (χ ψ : Character) (hχ : χ.residue≠1)
    (hmask : ∀ J : Ideal O, idealCoeff χ J=
      if IsCoprime J χ.modulus then idealCoeff ψ J else 0) (s : ℂ) :
    LFunction χ s=LFunction ψ s*factors χ.modulus ψ s := by
  have hψ : ψ.residue≠1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
  have ha := LFunction_entire_nonprincipal χ hχ
  have hb : Differentiable ℂ (fun z => LFunction ψ z*factors χ.modulus ψ z) :=
    (LFunction_entire_nonprincipal ψ hψ).mul (factors_differentiable _ _)
  have he : LFunction χ=(fun z => LFunction ψ z*factors χ.modulus ψ z) := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr ha).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hb) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ)<(2 : ℂ).re)] with z hz
    exact LFunction_eq_of_mask_right χ ψ hmask hz
  exact congr_fun he s

theorem original_reflected_bound : ∃ C : ℝ, 0<C ∧ ∀ χ ψ : Character,
    FiniteFourier.IsPrimitiveOnIdeals ψ.residue → χ.residue≠1 →
    (∀ J : Ideal O, idealCoeff χ J=
      if IsCoprime J χ.modulus then idealCoeff ψ J else 0) →
    ∀ s : ℂ, -(1/10 : ℝ)≤s.re → s.re≤1/2 →
    ‖LFunction χ s‖≤C*(ψ.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
      ‖LFunction χ (1-conj s)‖*
      (‖factors χ.modulus ψ s‖*‖(factors χ.modulus ψ (1-conj s))⁻¹‖) := by
  obtain ⟨C,hC,hbound⟩ := family_reflected_bound
  refine ⟨C,hC,?_⟩
  intro χ ψ hp hχ hmask s hl hr
  have hψ : ψ.residue≠1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
  have h := hbound ψ hp hψ s hl hr
  have hd : factors χ.modulus ψ (1-conj s)≠0 := factors_ne_zero _ _ (by simp; linarith)
  have he : LFunction ψ (1-conj s)=LFunction χ (1-conj s)*(factors χ.modulus ψ (1-conj s))⁻¹ := by
    rw [LFunction_eq_of_mask_entire χ ψ hχ hmask]
    field_simp
  rw [he,norm_mul] at h
  rw [LFunction_eq_of_mask_entire χ ψ hχ hmask,norm_mul]
  calc
    _ ≤ (C*(ψ.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
        (‖LFunction χ (1-conj s)‖*‖(factors χ.modulus ψ (1-conj s))⁻¹‖))*
          ‖factors χ.modulus ψ s‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = _ := by ring

theorem original_reflected_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ χ : Character, χ.residue≠1 →
    ∀ s : ℂ, -(1/10 : ℝ)≤s.re → s.re≤1/2 →
    ‖LFunction χ s‖≤C*(χ.modulus.absNorm : ℝ)^(1/2-s.re)*
      ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε)*
      (3+|s.im|)^2*‖LFunction χ (1-conj s)‖ := by
  obtain ⟨Cg,hCg,hreflect⟩ := original_reflected_bound
  obtain ⟨Cl,hCl,hleft⟩ := HeckeDeletionBounds.factors_any_re_subpower_bound ε hε
  obtain ⟨Cr,hCr,hright⟩ := HeckeDeletionBounds.factors_radical_subpower_bound (1/2) ε (by norm_num) hε
  refine ⟨Cg*Cl*Cr,by positivity,?_⟩
  intro χ hχ s hl hr
  obtain ⟨ψ,_,hp,hQ,hmask⟩ := exists_primitive_character χ
  have hR : 0<((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (HeckeDeletionBounds.radical_ne_zero χ.modulus))
  have hd₁ := hleft χ.modulus ψ s
  have hd₂ : ‖(factors χ.modulus ψ (1-conj s))⁻¹‖≤
      Cr*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε := by
    have h := hright χ.modulus ψ (1-conj s) (by simp; linarith)
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans h
  have hd : ‖factors χ.modulus ψ s‖*‖(factors χ.modulus ψ (1-conj s))⁻¹‖≤
      (Cl*Cr)*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε) := by
    calc
      _ ≤ (Cl*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+ε))*
          (Cr*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε) :=
        mul_le_mul hd₁ hd₂ (norm_nonneg _) (mul_nonneg hCl.le (Real.rpow_nonneg hR.le _))
      _ = _ := by
        have he : ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+ε)*
            ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε =
            ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε) := by
          rw [←Real.rpow_add hR]
          congr 1
          ring
        calc
          _ = (Cl*Cr)*(((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+ε)*
              ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε) := by ring
          _ = _ := by rw [he]
  have hQ' : (ψ.modulus.absNorm : ℝ)^(1/2-s.re)≤(χ.modulus.absNorm : ℝ)^(1/2-s.re) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQ) (by linarith)
  calc
    _ ≤ Cg*(ψ.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
        ‖LFunction χ (1-conj s)‖*
        (‖factors χ.modulus ψ s‖*‖(factors χ.modulus ψ (1-conj s))⁻¹‖) :=
      hreflect χ ψ hp hχ hmask s hl hr
    _ ≤ Cg*(χ.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
        ‖LFunction χ (1-conj s)‖*
        ((Cl*Cr)*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε)) := by
      apply mul_le_mul _ hd (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
      gcongr
    _ = _ := by ring

end SevenEighths.HeckeDyadicReflection

end

end OAI

end Source711

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DyadicReflectedControl.lean; sha256: 03f9e40ed1b004dd5aca0419ab6e73369a6186d3234b0d52aa5eb1c2b9f08d42 -/
section Source712
namespace OAI

noncomputable section
open scoped Classical Topology ComplexConjugate
open Complex Set
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeReciprocalGrowth HeckeDeletionBounds HeckeDyadicReflection

theorem radical_norm_ge_one (M : Ideal O) : 1≤((radical M).absNorm : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero M))

theorem buffered_reflected_line_control (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (s : ℂ), s.re=1-a-6*e → |s.im|≤(3*i+2 : ℕ)*T →
      ‖LFunction (χ j) s‖≤C*((χ j).modulus.absNorm : ℝ)^(a-1/2+6*e)*
        ((radical (χ j).modulus).absNorm : ℝ)^(6*e+2*ε)*
        (3+(3*i+2 : ℕ)*T)^2*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε := by
  obtain ⟨Cg,hCg,hreflect⟩ := original_reflected_subpower ε hε
  obtain ⟨Cb,hCb,hrect⟩ := buffered_rectangle_control e ε he he' hε
  refine ⟨Cg*Cb,mul_pos hCg hCb,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j s hs him
  have hwre : (1-conj s).re=a+6*e := by simp; linarith
  have hwim : (1-conj s).im=s.im := by simp
  have hw := hrect χ hχ T a i hT ha ha' hmax j (1-conj s)
    (by rw [hwre]) (by rw [hwre]; linarith) (by rwa [hwim])
  have hL : ‖LFunction (χ j) (1-conj s)‖≤
      Cb*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans hw.2
  have href := hreflect (χ j) (hχ j) s (by rw [hs]; linarith) (by rw [hs]; linarith)
  have hexp : 1/2-s.re=a-1/2+6*e := by rw [hs]; ring
  rw [hexp] at href
  have hR : ((radical (χ j).modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε)≤
      ((radical (χ j).modulus).absNorm : ℝ)^(6*e+2*ε) := by
    apply Real.rpow_le_rpow_of_exponent_le (radical_norm_ge_one _)
    have hm : max (-s.re) 0≤6*e := max_le (by rw [hs]; linarith) (by positivity)
    linarith
  calc
    _ ≤ Cg*((χ j).modulus.absNorm : ℝ)^(a-1/2+6*e)*
        ((radical (χ j).modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε)*
        (3+|s.im|)^2*‖LFunction (χ j) (1-conj s)‖ := href
    _ ≤ Cg*((χ j).modulus.absNorm : ℝ)^(a-1/2+6*e)*
        ((radical (χ j).modulus).absNorm : ℝ)^(6*e+2*ε)*
        (3+(3*i+2 : ℕ)*T)^2*(Cb*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε) := by
      gcongr
    _ = _ := by ring

theorem original_upper_strip (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ χ : Character, χ.residue≠1 → ∀ s : ℂ,
      -(1/10 : ℝ)≤s.re →
      ‖LFunction χ s‖≤C*(χ.modulus.absNorm : ℝ)^(3/5 : ℝ)*
        ((radical χ.modulus).absNorm : ℝ)^(1/10+ε)*(3+|s.im|)^2 := by
  obtain ⟨Cd,hCd,hdel⟩ := factors_any_re_subpower_bound ε hε
  refine ⟨(1+HeckeLogarithmicInput.uniformConstant)*Cd,
    mul_pos (by linarith [HeckeLogarithmicInput.uniformConstant_nonneg]) hCd,?_⟩
  intro χ hχ s hs
  obtain ⟨ψ,_,hp,hQ,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue≠1 := fun h => hχ ((HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mpr h)
  have hg := HeckeLogarithmicInput.regular_right_growth ψ hp hs
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal ψ hψ] at hg
  have hQ' : (ψ.modulus.absNorm : ℝ)^(3/5 : ℝ)≤(χ.modulus.absNorm : ℝ)^(3/5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQ) (by norm_num)
  have hd : ‖HeckeFiniteDeletion.factors χ.modulus ψ s‖≤
      Cd*((radical χ.modulus).absNorm : ℝ)^(1/10+ε) := by
    apply (hdel χ.modulus ψ s).trans
    apply mul_le_mul_of_nonneg_left _ hCd.le
    apply Real.rpow_le_rpow_of_exponent_le (radical_norm_ge_one _)
    have hm : max (-s.re) 0≤1/10 := max_le (by linarith) (by norm_num)
    linarith
  have hU := HeckeLogarithmicInput.uniformConstant_nonneg
  rw [LFunction_eq_of_mask_entire χ ψ hχ hmask,norm_mul]
  calc
    _ ≤ (HeckeLogarithmicInput.uniformConstant*(ψ.modulus.absNorm : ℝ)^(3/5 : ℝ)*(3+|s.im|)^2)*
        (Cd*((radical χ.modulus).absNorm : ℝ)^(1/10+ε)) :=
      mul_le_mul hg hd (norm_nonneg _) (by positivity)
    _ ≤ ((1+HeckeLogarithmicInput.uniformConstant)*(χ.modulus.absNorm : ℝ)^(3/5 : ℝ)*(3+|s.im|)^2)*
        (Cd*((radical χ.modulus).absNorm : ℝ)^(1/10+ε)) := by
      gcongr
      linarith
    _ = _ := by ring

end SevenEighths.HeckeDyadic

end

end OAI

end Source712

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DyadicReflectedPointwise.lean; sha256: 4252086123f81faa3692095e5a3f83b1d0af84d2577c6989a3bc217ae5ba912b -/
section Source713
namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeReciprocalGrowth HeckeDeletionBounds

theorem reflected_polynomial_bound (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ Cg Cr : ℝ, 0<Cg ∧ 0<Cr ∧
    ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (W : ℝ → ℂ) (A B : ℝ),
      0<A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ (D σ freq V C₂ Cn : ℝ) (n : ℕ), 1≤D → 0≤V →
      |freq|+V≤(3*i+2 : ℕ)*T → 0≤C₂ → 0≤Cn →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((1-a-6*e-σ : ℝ) : ℂ)+t*I)‖≤C₂) →
      (∀ x ∈ Icc (1-a-6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn) →
      let H := (3*i+2 : ℕ)*T
      let Q := ((χ j).modulus.absNorm : ℝ)
      let R := ((radical (χ j).modulus).absNorm : ℝ)
      let Kg := Cg*Q^(3/5 : ℝ)*R^(1/10+ε)*(3+H)^2
      let Kr := Cr*Q^(a-1/2+6*e)*R^(6*e+2*ε)*(3+H)^2*
        (presentationComplexity (χ j) H)^ε
      ‖polynomial (χ j) false W D σ freq‖≤(1/(2*Real.pi))*
        (C₂*D^(1/2-a-6*e)*Kr*Real.pi +
         2*(Cn*D^(3/2 : ℝ)*Kg/(1+V)^n)*|1+a+6*e| +
         (Cn*D^(3/2 : ℝ)*HeckeReciprocalBound.bound 2)/(1+V)^n*Real.pi) := by
  obtain ⟨Cg,hCg,hglobal⟩ := original_upper_strip ε hε
  obtain ⟨Cr,hCr,hreflect⟩ := buffered_reflected_line_control e ε he he' hε
  refine ⟨Cg,Cr,hCg,hCr,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j W A B hA hWs hW
    D σ freq V C₂ Cn n hD hV hfreq hC₂ hCn hm₂ hmn
  dsimp only
  let H : ℝ := (3*i+2 : ℕ)*T
  let Q : ℝ := (χ j).modulus.absNorm
  let R : ℝ := (radical (χ j).modulus).absNorm
  let Kg := Cg*Q^(3/5 : ℝ)*R^(1/10+ε)*(3+H)^2
  let Kr := Cr*Q^(a-1/2+6*e)*R^(6*e+2*ε)*(3+H)^2*
    (presentationComplexity (χ j) H)^ε
  have hKg : 0≤Kg := by dsimp [Kg,Q,R]; positivity
  have hKr : 0≤Kr := by dsimp [Kr,Q,R,presentationComplexity,HeckeLogarithmic.complexity]; positivity
  have hlr : 1-a-6*e-σ≤2-σ := by linarith
  have hmem {s : ℂ} (hs : s ∈ (uIcc (1-a-6*e-σ) (2-σ) ×ℂ uIcc (-V) V)) :
      1-a-6*e≤(s+shift σ freq).re ∧ (s+shift σ freq).re≤2 ∧ |(s+shift σ freq).im|≤H := by
    have h := translated_rectangle_mem (a:=1-a-12*e) (e:=e) (σ:=σ) (freq:=freq)
      (by linarith : 1-a-12*e+6*e≤1-a-6*e-σ+σ)
      (by linarith : 2-σ+σ≤2) hlr hV hfreq hs
    constructor
    · linarith [h.1]
    · exact h.2
  have hseries (s : ℂ) (hs : s ∈ (uIcc (1-a-6*e-σ) (2-σ) ×ℂ uIcc (-V) V)) :
      ‖series (χ j) false (s+shift σ freq)‖≤Kg := by
    have h := hglobal (χ j) (hχ j) (s+shift σ freq) (by linarith [(hmem hs).1])
    apply h.trans
    dsimp [Kg,Q,R]
    gcongr
    exact (hmem hs).2.2
  have hcentral (t : ℝ) (ht : t∈Icc (-V) V) :
      ‖series (χ j) false (((1-a-6*e-σ : ℝ) : ℂ)+t*I+shift σ freq)‖≤Kr := by
    have him : |t-freq|≤H := (abs_sub _ _).trans (by
      have ht' := abs_le.mpr ht
      change |t|+|freq|≤H
      linarith)
    apply hreflect χ hχ T a i hT ha ha' hmax j
    · simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,mul_zero,I_im,zero_mul,
        sub_self,add_zero,shift_re]
      ring
    · simpa [shift,sub_eq_add_neg,H] using him
  have hb := polynomial_bound_of_rectangle_split (χ j) (hχ j) false W A B hA hWs hW
    D σ freq (1-a-6*e-σ) (2-σ) V C₂ Cn Kg Kr n hD hlr (by linarith)
    hV hC₂ hCn hKg hKr hm₂ hmn hcentral (fun _ _ h => Bool.false_ne_true h |>.elim) hseries
  dsimp only [Kg,Kr,Q,R,H] at hb
  convert hb using 1 ; congr 2 <;> ring_nf

end SevenEighths.HeckeDyadic

end

end OAI

end Source713

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DyadicScale.lean; sha256: ac9c335a1ed84aa17ecc893157c92165fe7d5dcf10c29f9c9eb386c6be48e73e -/
section Source714
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeDeletionBounds HeckeReciprocalGrowth HeckeLogarithmic

theorem radical_dvd (M : Ideal O) (hM : M≠0) : radical M∣M := by
  unfold radical SmoothMobiusCorrection.primeProduct
  rw [SmoothMobiusCorrection.prod_primeSet M (fun J : Ideal O => J)]
  exact IdealMobiusDivisorSum.support_product_dvd hM (Finset.Subset.refl _)

theorem radical_norm_le_modulus (χ : Character) :
    ((radical χ.modulus).absNorm : ℝ)≤χ.modulus.absNorm := by
  exact_mod_cast Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot))
    (map_dvd Ideal.absNorm (radical_dvd χ.modulus χ.modulus_ne_bot))

theorem presentationComplexity_le_of_modulus_le (χ : Character) (U H : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤U) :
    presentationComplexity χ H≤2*U^2*(3+|H|)^2 := by
  have hR := (radical_norm_le_modulus χ).trans hQ
  have hU : 0≤U := (Nat.cast_nonneg χ.modulus.absNorm).trans hQ
  unfold presentationComplexity complexity
  calc
    _ ≤ U*(2*U*(3+|H|)^2) := by gcongr
    _ = _ := by ring

theorem reflected_conductor_cost (χ : Character) (U a e ε : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤U) (ha : 1/2≤a) (he : 0≤e) (hε : 0≤ε) :
    (χ.modulus.absNorm : ℝ)^(a-1/2+6*e)*
      ((radical χ.modulus).absNorm : ℝ)^(6*e+2*ε)≤U^(a-1/2+12*e+2*ε) := by
  have hU : 0<U := lt_of_lt_of_le zero_lt_one
    ((HeckeLogarithmicInput.modulus_norm_ge_one χ).trans hQ)
  have hR := (radical_norm_le_modulus χ).trans hQ
  calc
    _ ≤ U^(a-1/2+6*e)*U^(6*e+2*ε) :=
      mul_le_mul (Real.rpow_le_rpow (by positivity) hQ (by linarith))
        (Real.rpow_le_rpow (by positivity) hR (by positivity))
        (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hU.le _)
    _ = _ := by
      rw [←Real.rpow_add hU]
      congr 1
      ring

theorem positive_scale_exponent (U a e r : ℝ) (hU : 0<U) :
    (U^r)^(a+6*e-1/2)=U^((a-1/2+6*e)*r) := by
  rw [←Real.rpow_mul hU.le]
  congr 1
  ring

theorem reflected_scale_exponent (U a e ε m : ℝ) (hU : 0<U) :
    U^(a-1/2+12*e+2*ε)*(U^m)^(1/2-a-6*e)=
      U^((a-1/2)*(1-m)+6*e*(2-m)+2*ε) := by
  rw [←Real.rpow_mul hU.le,←Real.rpow_add hU]
  congr 1
  ring

end SevenEighths.HeckeDyadic

end

end OAI

end Source714

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DyadicTailBudget.lean; sha256: f58fdd3249b3e9022fc5185928ac778b9daf5bfab923d98abd18464709017fe8 -/
section Source715
namespace OAI

noncomputable section
namespace SevenEighths.HeckeDyadic

theorem exists_external_tail_order (τ B p : ℝ) (hτ : 0<τ) :
    ∃ n : ℕ, ∀ Z : ℝ, 1≤Z → Z^B/(1+Z^τ)^n≤Z^p := by
  obtain ⟨n,hn⟩ := exists_nat_gt ((B-p)/τ)
  refine ⟨n,?_⟩
  intro Z hZ
  have hZp : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hn' : B≤p+τ*(n : ℝ) := by
    have h := (div_lt_iff₀ hτ).mp hn
    nlinarith
  have hden : 0<(1+Z^τ)^n := by positivity
  apply (div_le_iff₀ hden).mpr
  calc
    Z^B ≤ Z^(p+τ*(n : ℝ)) := Real.rpow_le_rpow_of_exponent_le hZ hn'
    _ = Z^p*(Z^τ)^n := by
      rw [Real.rpow_add hZp,Real.rpow_mul hZp.le,Real.rpow_natCast]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.rpow_nonneg hZp.le _) (by linarith) n)
      (Real.rpow_nonneg hZp.le _)

theorem constant_absorbed_eventually (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in Filter.atTop, C≤Z^ε := by
  exact (tendsto_rpow_atTop hε).eventually (Filter.eventually_ge_atTop C)

theorem uniform_external_tail_order (τ dmax B R : ℝ)
    (hτ : 0<τ) (_hdmax : 0≤dmax) (hB : 0≤B) (hR : 0≤R) :
    ∃ n : ℕ, ∀ Z d p : ℝ, 1≤Z → 0≤d → d≤dmax → -R≤p →
      (Z^d)^B/(1+Z^τ/2)^n≤(2 : ℝ)^n*(Z^d)^p := by
  obtain ⟨n,hn⟩ := exists_external_tail_order τ (dmax*B) (-dmax*R) hτ
  refine ⟨n,?_⟩
  intro Z d p hZ hd hd' hp
  have hZp : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hnum : (Z^d)^B≤Z^(dmax*B) := by
    rw [←Real.rpow_mul hZp.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ (mul_le_mul_of_nonneg_right hd' hB)
  have htarget : Z^(-dmax*R)≤(Z^d)^p := by
    rw [←Real.rpow_mul hZp.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    nlinarith [mul_nonneg hd (show 0≤p+R by linarith),
      mul_nonneg (show 0≤dmax-d by linarith) hR]
  have hden : ((1+Z^τ)/2)^n≤(1+Z^τ/2)^n :=
    pow_le_pow_left₀ (by positivity) (by linarith) n
  calc
    _ ≤ (Z^(dmax*B))/((1+Z^τ)/2)^n :=
      div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = (2 : ℝ)^n*(Z^(dmax*B)/(1+Z^τ)^n) := by
      rw [div_pow]
      field_simp
    _ ≤ (2 : ℝ)^n*Z^(-dmax*R) := mul_le_mul_of_nonneg_left (hn Z hZ) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left htarget (by positivity)

end SevenEighths.HeckeDyadic

end

end OAI

end Source715

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DyadicCentralBudget.lean; sha256: ea70a0f2b24ba698ca30d97f55383a796b377cc434de9e506adc5d750f1d88e6 -/
section Source716
namespace OAI

noncomputable section
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeDeletionBounds HeckeReciprocalGrowth HeckeLogarithmic

theorem presentation_cost (χ : Character) (U H ε : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤U) (hH : 0≤H) (hε : 0≤ε) (hε' : ε≤1) :
    (presentationComplexity χ H)^ε≤2*U^(2*ε)*(3+H)^2 := by
  have hU : 1≤U := (HeckeLogarithmicInput.modulus_norm_ge_one χ).trans hQ
  have hbase : 1≤3+H := by linarith
  have hc := presentationComplexity_le_of_modulus_le χ U H hQ
  rw [abs_of_nonneg hH] at hc
  have hp : (presentationComplexity χ H)^ε≤(2*U^2*(3+H)^2)^ε :=
    Real.rpow_le_rpow (by unfold presentationComplexity complexity; positivity) hc hε
  have he : (2*U^2*(3+H)^2)^ε=(2 : ℝ)^ε*U^(2*ε)*(3+H)^(2*ε) := by
    rw [Real.mul_rpow (by positivity) (by positivity),Real.mul_rpow (by norm_num) (by positivity)]
    simp only [←Real.rpow_natCast,←Real.rpow_mul (by linarith : 0≤U),
      ←Real.rpow_mul (by linarith : 0≤3+H),Nat.cast_ofNat]
  rw [he] at hp
  have h2 : (2 : ℝ)^ε≤2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2) hε'
  have hh : (3+H)^(2*ε)≤(3+H)^2 := by
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hbase (by norm_num; linarith)
  exact hp.trans (mul_le_mul (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (by linarith) _))
    hh (Real.rpow_nonneg (by linarith) _) (by positivity))

theorem positive_central_cost (χ : Character) (U H a e ε η r : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤U) (hH : 0≤H) (hε : 0≤ε) (hε' : ε≤1)
    (hheight : (3+H)^4≤U^η) :
    (U^r)^(a+6*e-1/2)*(presentationComplexity χ H)^ε≤
      2*U^((a-1/2+6*e)*r+2*ε+η) := by
  have hU : 0<U := lt_of_lt_of_le zero_lt_one ((HeckeLogarithmicInput.modulus_norm_ge_one χ).trans hQ)
  have hh : (3+H)^2≤U^η := by
    apply le_trans _ hheight
    exact pow_le_pow_right₀ (by linarith) (by decide : 2≤4)
  calc
    _ ≤ (U^r)^(a+6*e-1/2)*(2*U^(2*ε)*U^η) :=
      mul_le_mul_of_nonneg_left ((presentation_cost χ U H ε hQ hH hε hε').trans
        (mul_le_mul_of_nonneg_left hh (by positivity))) (by positivity)
    _ = _ := by
      rw [positive_scale_exponent U a e r hU]
      rw [Real.rpow_add hU,Real.rpow_add hU]
      ring

theorem reflected_central_cost (χ : Character) (U H a e ε η m : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤U) (hH : 0≤H) (ha : 1/2≤a)
    (he : 0≤e) (hε : 0≤ε) (hε' : ε≤1) (hheight : (3+H)^4≤U^η) :
    (χ.modulus.absNorm : ℝ)^(a-1/2+6*e)*
      ((radical χ.modulus).absNorm : ℝ)^(6*e+2*ε)*(3+H)^2*
      (presentationComplexity χ H)^ε*(U^m)^(1/2-a-6*e)≤
      2*U^((a-1/2)*(1-m)+6*e*(2-m)+4*ε+η) := by
  have hU : 0<U := lt_of_lt_of_le zero_lt_one ((HeckeLogarithmicInput.modulus_norm_ge_one χ).trans hQ)
  have hcost := reflected_conductor_cost χ U a e ε hQ ha he hε
  have hcomplex := presentation_cost χ U H ε hQ hH hε hε'
  have hcomplex0 : 0≤(presentationComplexity χ H)^ε := Real.rpow_nonneg (by
    unfold presentationComplexity complexity
    positivity) _
  calc
    _ ≤ U^(a-1/2+12*e+2*ε)*(3+H)^2*(2*U^(2*ε)*(3+H)^2)*(U^m)^(1/2-a-6*e) := by
      gcongr
    _ = 2*(U^(a-1/2+12*e+2*ε)*(U^m)^(1/2-a-6*e))*U^(2*ε)*(3+H)^4 := by ring
    _ ≤ 2*(U^(a-1/2+12*e+2*ε)*(U^m)^(1/2-a-6*e))*U^(2*ε)*U^η :=
      mul_le_mul_of_nonneg_left hheight (by positivity)
    _ = _ := by
      rw [reflected_scale_exponent U a e ε m hU]
      calc
        _ = 2*(U^((a-1/2)*(1-m)+6*e*(2-m)+2*ε)*U^(2*ε)*U^η) := by ring
        _ = 2*U^(((a-1/2)*(1-m)+6*e*(2-m)+2*ε)+2*ε+η) := by
          rw [←Real.rpow_add hU,←Real.rpow_add hU]
        _ = _ := by congr 2; ring

theorem direct_external_cost (χ : Character) (U H κ η r R : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤U) (hH : 0≤H) (hκ : 0≤κ) (hκ' : κ≤1)
    (hr : 0≤r) (hrR : r≤R) (hheight : (3+H)^4≤U^η) :
    (U^r)^(3/2 : ℝ)*(presentationComplexity χ H)^κ≤2*U^(2*R+2+η) := by
  have hU : 1≤U := (HeckeLogarithmicInput.modulus_norm_ge_one χ).trans hQ
  have h := positive_central_cost χ U H 2 0 κ η r hQ hH hκ hκ' hheight
  norm_num only [mul_zero,add_zero] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le hU
  nlinarith

theorem reflected_external_cost (χ : Character) (U H κ η r R : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤U) (hH : 0≤H) (hκ : 0≤κ) (hκ' : κ≤1)
    (hr : 0≤r) (hrR : r≤R) (hheight : (3+H)^4≤U^η) :
    (U^r)^(3/2 : ℝ)*(χ.modulus.absNorm : ℝ)^(3/5 : ℝ)*
      ((radical χ.modulus).absNorm : ℝ)^(1/10+κ)*(3+H)^2≤U^(2*R+2+η) := by
  have hU : 1≤U := (HeckeLogarithmicInput.modulus_norm_ge_one χ).trans hQ
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hR := (radical_norm_le_modulus χ).trans hQ
  have hh : (3+H)^2≤U^η :=
    (pow_le_pow_right₀ (by linarith) (by decide : 2≤4)).trans hheight
  calc
    _ ≤ (U^r)^(3/2 : ℝ)*U^(3/5 : ℝ)*U^(1/10+κ)*U^η := by
      gcongr
    _ = U^(r*(3/2)+(3/5)+(1/10+κ)+η) := by
      rw [←Real.rpow_mul hUp.le,←Real.rpow_add hUp,←Real.rpow_add hUp,←Real.rpow_add hUp]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)

end SevenEighths.HeckeDyadic

end

end OAI

end Source716

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DyadicLossBudget.lean; sha256: 9488cc14894c68cd9a014d4de033f35ca8da14a796998a2be4b5f811a2c6b1e0 -/
section Source717
namespace OAI

noncomputable section
namespace SevenEighths.HeckeDyadic

theorem central_squared_exponents (R a e κ η ε r m : ℝ)
    (hR : 0≤R) (he : 0≤e) (hκ : 0≤κ) (_hη : 0≤η)
    (hr : r≤R) (hm : 0≤m)
    (hbudget : 12*e*(R+2)+8*κ+2*η≤ε) :
    2*((a-1/2+6*e)*r+2*κ+η)≤(2*a-1)*r+ε ∧
    2*((a-1/2)*(1-m)+6*e*(2-m)+4*κ+η)≤(2*a-1)*(1-m)+ε := by
  have hEr : e*r≤e*R := mul_le_mul_of_nonneg_left hr he
  have hEm : 0≤e*m := mul_nonneg he hm
  have hER : 0≤e*R := mul_nonneg he hR
  constructor <;> nlinarith

theorem exists_central_loss_parameters (R ε : ℝ) (hR : 0≤R) (hε : 0<ε) :
    ∃ e₀ κ η : ℝ, 0<e₀ ∧ e₀≤1/1000 ∧ 0<κ ∧ κ≤1 ∧ 0<η ∧
      ∀ e : ℝ, 0<e → e<e₀ → 12*e*(R+2)+8*κ+2*η≤ε/2 := by
  let e₀ : ℝ := min (1/1000) (ε/(96*(R+2)))
  let κ : ℝ := min (1/2) (ε/64)
  let η : ℝ := ε/16
  have hRp : 0<R+2 := by linarith
  have he₀ : 0<e₀ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hκ : 0<κ := lt_min (by norm_num) (div_pos hε (by norm_num))
  refine ⟨e₀,κ,η,he₀,min_le_left _ _,hκ,(min_le_left _ _).trans (by norm_num),
    div_pos hε (by norm_num),?_⟩
  intro e he he'
  have heb : e≤ε/(96*(R+2)) := he'.le.trans (min_le_right _ _)
  have heb' := (le_div_iff₀ (by positivity : 0<96*(R+2))).mp heb
  have hκb : κ≤ε/64 := min_le_right _ _
  dsimp only [η]
  nlinarith

theorem indexed_height_bound (i I : ℕ) (hi : i≤I) (T : ℝ) (hT : 0≤T) :
    (3+(3*i+2 : ℕ)*T)^4≤(3*(I : ℝ)+5)^4*(1+T)^4 := by
  have hi' : (i : ℝ)≤I := by exact_mod_cast hi
  have hlin : 3+(3*i+2 : ℕ)*T≤(3*(I : ℝ)+5)*(1+T) := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hi' hT,Nat.cast_nonneg (α:=ℝ) I]
  calc
    _ ≤ ((3*(I : ℝ)+5)*(1+T))^4 := pow_le_pow_left₀ (by positivity) hlin 4
    _ = _ := mul_pow _ _ _

theorem min_plain_bound (X C U δ m ε : ℝ)
    (h₁ : X≤C*U^(δ*m+ε)) (h₂ : X≤C*U^(δ*(1-m)+ε)) :
    X≤C*U^(δ*min m (1-m)+ε) := by
  rcases le_total m (1-m) with h | h
  · simpa only [min_eq_left h] using h₁
  · simpa only [min_eq_right h] using h₂

theorem squared_bound_of_central_and_error (z : ℂ) (U C E p b ε : ℝ)
    (hU : 1≤U) (hC : 0≤C) (hE : 0≤E) (hε : 0≤ε)
    (hb : 2*b≤ε)
    (hz : ‖z‖≤C*U^(p+b)+E*U^p) :
    ‖z‖^2≤(C+E)^2*U^(2*p+ε) := by
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hp₁ : U^(p+b)≤U^(p+ε/2) :=
    Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  have hp₂ : U^p≤U^(p+ε/2) :=
    Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  have hn : ‖z‖≤(C+E)*U^(p+ε/2) := by
    calc
      _ ≤ C*U^(p+b)+E*U^p := hz
      _ ≤ C*U^(p+ε/2)+E*U^(p+ε/2) := add_le_add
        (mul_le_mul_of_nonneg_left hp₁ hC) (mul_le_mul_of_nonneg_left hp₂ hE)
      _ = _ := by ring
  calc
    _ ≤ ((C+E)*U^(p+ε/2))^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = _ := by
      have hp : (U^(p+ε/2))^2=U^(2*p+ε) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hUp.le]
        congr 1
        norm_num
        ring
      rw [mul_pow,hp]

end SevenEighths.HeckeDyadic

end

end OAI

end Source717

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DyadicScaled.lean; sha256: e1576b4de60dd2ad77d5caf81c7ad870e21cf3c7f25c3713842e9fa3b8a7eeeb -/
section Source718
namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeReciprocalGrowth

theorem scaled_direct_bound (e κ : ℝ) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hκ' : κ≤1) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (inverse : Bool) (W : ℝ → ℂ) (A B : ℝ),
      0<A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ (U r R η σ freq V C₂ Cn : ℝ) (n : ℕ),
      (χ j).modulus.absNorm≤U → 0≤r → r≤R → 0≤η → 0≤V →
      |freq|+V≤(3*i+2 : ℕ)*T → (3+(3*i+2 : ℕ)*T)^4≤U^η → 0≤C₂ → 0≤Cn →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((a+6*e-σ : ℝ) : ℂ)+t*I)‖≤C₂) →
      (∀ x ∈ Icc (a+6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn) →
      ‖polynomial (χ j) inverse W (U^r) σ freq‖≤
        C*C₂*U^((a-1/2+6*e)*r+2*κ+η)+C*Cn*U^(2*R+2+η)/(1+V)^n := by
  obtain ⟨Cb,hCb,hbound⟩ := buffered_polynomial_bound e κ he he' hκ
  let E := HeckeReciprocalBound.bound 2
  have hE : 0≤E := tsum_nonneg (fun _ => norm_nonneg _)
  let C := 1+2*Cb*Real.pi+8*Cb+E*Real.pi
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j inverse W A B hA hWs hW
    U r R η σ freq V C₂ Cn n hQ hr hrR hη hV hfreq hheight hC₂ hCn hm₂ hmn
  let H : ℝ := (3*i+2 : ℕ)*T
  have hH : 0≤H := by dsimp [H]; positivity
  have hU : 1≤U := (HeckeLogarithmicInput.modulus_norm_ge_one (χ j)).trans hQ
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hD : 1≤U^r := Real.one_le_rpow hU hr
  have hb := hbound χ hχ T a i hT ha ha' hmax j inverse W A B hA hWs hW
    (U^r) σ freq V C₂ Cn n hD hV hfreq hC₂ hCn hm₂ hmn
  dsimp only at hb
  have hcentral := positive_central_cost (χ j) U H a e κ η r hQ hH hκ.le hκ' hheight
  have hexternal := direct_external_cost (χ j) U H κ η r R hQ hH hκ.le hκ' hr hrR hheight
  have hpow : (U^r)^(3/2 : ℝ)≤U^(2*R+2+η) := by
    rw [←Real.rpow_mul hUp.le]
    exact Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)
  have hwidth : |2-a-6*e|≤2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hc : C₂*(U^r)^(a+6*e-1/2)*(Cb*(presentationComplexity (χ j) H)^κ)*Real.pi≤
      (2*Cb*Real.pi)*C₂*U^((a-1/2+6*e)*r+2*κ+η) := by
    calc
      _ = (C₂*Cb*Real.pi)*((U^r)^(a+6*e-1/2)*(presentationComplexity (χ j) H)^κ) := by ring
      _ ≤ (C₂*Cb*Real.pi)*(2*U^((a-1/2+6*e)*r+2*κ+η)) :=
        mul_le_mul_of_nonneg_left hcentral (by positivity)
      _ = _ := by ring
  have hj : 2*(Cn*(U^r)^(3/2 : ℝ)*(Cb*(presentationComplexity (χ j) H)^κ)/(1+V)^n)*|2-a-6*e|≤
      (8*Cb)*Cn*U^(2*R+2+η)/(1+V)^n := by
    calc
      _ = 2*Cn*Cb*((U^r)^(3/2 : ℝ)*(presentationComplexity (χ j) H)^κ)/(1+V)^n*|2-a-6*e| := by ring
      _ ≤ 2*Cn*Cb*(2*U^(2*R+2+η))/(1+V)^n*2 := by gcongr
      _ = _ := by ring
  have ht : (Cn*(U^r)^(3/2 : ℝ)*E)/(1+V)^n*Real.pi≤
      (E*Real.pi)*Cn*U^(2*R+2+η)/(1+V)^n := by
    calc
      _ ≤ (Cn*U^(2*R+2+η)*E)/(1+V)^n*Real.pi := by gcongr
      _ = _ := by ring
  have hfac : 1/(2*Real.pi)≤(1 : ℝ) := by
    apply (div_le_one (by positivity)).mpr
    linarith [Real.pi_gt_three]
  have hcomp : 0≤(presentationComplexity (χ j) H)^κ := Real.rpow_nonneg (by
    unfold presentationComplexity HeckeLogarithmic.complexity
    positivity) _
  apply (hb.trans (mul_le_of_le_one_left (by positivity) hfac)).trans
  change _ ≤ _ at hc hj ht
  have hcC : 2*Cb*Real.pi≤C := by dsimp [C]; nlinarith [mul_nonneg hE Real.pi_pos.le]
  have heC : 8*Cb+E*Real.pi≤C := by dsimp [C]; nlinarith [Real.pi_pos]
  calc
    _ ≤ (2*Cb*Real.pi)*C₂*U^((a-1/2+6*e)*r+2*κ+η)+
        (8*Cb)*Cn*U^(2*R+2+η)/(1+V)^n+(E*Real.pi)*Cn*U^(2*R+2+η)/(1+V)^n := by
      exact add_le_add (add_le_add hc hj) ht
    _ = (2*Cb*Real.pi)*C₂*U^((a-1/2+6*e)*r+2*κ+η)+
        (8*Cb+E*Real.pi)*Cn*U^(2*R+2+η)/(1+V)^n := by ring
    _ ≤ _ := by gcongr

end SevenEighths.HeckeDyadic

end

end OAI

end Source718

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DyadicScaledReflection.lean; sha256: 98ff7c446d1d1209dcbbf786e5d7e36150c4d9b727bed7a51a0db9caae64eb9e -/
section Source719
namespace OAI

noncomputable section

open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeReciprocalGrowth

theorem scaled_reflected_bound (e κ : ℝ) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hκ' : κ≤1) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (W : ℝ → ℂ) (A B : ℝ),
      0<A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ (U r R η σ freq V C₂ Cn : ℝ) (n : ℕ),
      (χ j).modulus.absNorm≤U → 0≤r → r≤R → 0≤η → 0≤V →
      |freq|+V≤(3*i+2 : ℕ)*T → (3+(3*i+2 : ℕ)*T)^4≤U^η → 0≤C₂ → 0≤Cn →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((1-a-6*e-σ : ℝ) : ℂ)+t*I)‖≤C₂) →
      (∀ x ∈ Icc (1-a-6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn) →
      ‖polynomial (χ j) false W (U^r) σ freq‖≤
        C*C₂*U^((a-1/2)*(1-r)+6*e*(2-r)+4*κ+η)+C*Cn*U^(2*R+2+η)/(1+V)^n := by
  obtain ⟨Cg,Cr,hCg,hCr,hbound⟩ := reflected_polynomial_bound e κ he he' hκ
  let E := HeckeReciprocalBound.bound 2
  have hE : 0≤E := tsum_nonneg (fun _ => norm_nonneg _)
  let C := 1+2*Cr*Real.pi+6*Cg+E*Real.pi
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j W A B hA hWs hW
    U r R η σ freq V C₂ Cn n hQ hr hrR hη hV hfreq hheight hC₂ hCn hm₂ hmn
  let H : ℝ := (3*i+2 : ℕ)*T
  have hH : 0≤H := by dsimp [H]; positivity
  have hU : 1≤U := (HeckeLogarithmicInput.modulus_norm_ge_one (χ j)).trans hQ
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hD : 1≤U^r := Real.one_le_rpow hU hr
  have hb := hbound χ hχ T a i hT ha ha' hmax j W A B hA hWs hW
    (U^r) σ freq V C₂ Cn n hD hV hfreq hC₂ hCn hm₂ hmn
  dsimp only at hb
  have hcentral := reflected_central_cost (χ j) U H a e κ η r hQ hH (by linarith) he.le hκ.le hκ' hheight
  have hexternal := reflected_external_cost (χ j) U H κ η r R hQ hH hκ.le hκ' hr hrR hheight
  have hpow : (U^r)^(3/2 : ℝ)≤U^(2*R+2+η) := by
    rw [←Real.rpow_mul hUp.le]
    exact Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)
  have hwidth : |1+a+6*e|≤3 := abs_le.mpr ⟨by linarith,by linarith⟩
  let Q : ℝ := (χ j).modulus.absNorm
  let Rad : ℝ := (HeckeDeletionBounds.radical (χ j).modulus).absNorm
  have hc : C₂*(U^r)^(1/2-a-6*e)*(Cr*Q^(a-1/2+6*e)*Rad^(6*e+2*κ)*(3+H)^2*
      (presentationComplexity (χ j) H)^κ)*Real.pi≤
      (2*Cr*Real.pi)*C₂*U^((a-1/2)*(1-r)+6*e*(2-r)+4*κ+η) := by
    calc
      _ = (C₂*Cr*Real.pi)*(Q^(a-1/2+6*e)*Rad^(6*e+2*κ)*(3+H)^2*
        (presentationComplexity (χ j) H)^κ*(U^r)^(1/2-a-6*e)) := by ring
      _ ≤ (C₂*Cr*Real.pi)*(2*U^((a-1/2)*(1-r)+6*e*(2-r)+4*κ+η)) :=
        mul_le_mul_of_nonneg_left hcentral (by positivity)
      _ = _ := by ring
  have hj : 2*(Cn*(U^r)^(3/2 : ℝ)*(Cg*Q^(3/5 : ℝ)*Rad^(1/10+κ)*(3+H)^2)/(1+V)^n)*|1+a+6*e|≤
      (6*Cg)*Cn*U^(2*R+2+η)/(1+V)^n := by
    calc
      _ = 2*Cn*Cg*((U^r)^(3/2 : ℝ)*Q^(3/5 : ℝ)*Rad^(1/10+κ)*(3+H)^2)/(1+V)^n*|1+a+6*e| := by ring
      _ ≤ 2*Cn*Cg*U^(2*R+2+η)/(1+V)^n*3 := by gcongr
      _ = _ := by ring
  have ht : (Cn*(U^r)^(3/2 : ℝ)*E)/(1+V)^n*Real.pi≤
      (E*Real.pi)*Cn*U^(2*R+2+η)/(1+V)^n := by
    calc
      _ ≤ (Cn*U^(2*R+2+η)*E)/(1+V)^n*Real.pi := by gcongr
      _ = _ := by ring
  have hfac : 1/(2*Real.pi)≤(1 : ℝ) := by
    apply (div_le_one (by positivity)).mpr
    linarith [Real.pi_gt_three]
  have hcomp : 0≤(presentationComplexity (χ j) H)^κ := Real.rpow_nonneg (by
    unfold presentationComplexity HeckeLogarithmic.complexity
    positivity) _
  apply (hb.trans (mul_le_of_le_one_left (by positivity) hfac)).trans
  change _ ≤ _ at hc hj ht
  have hcC : 2*Cr*Real.pi≤C := by dsimp [C]; nlinarith only [hCg,mul_nonneg hE Real.pi_pos.le]
  have heC : 6*Cg+E*Real.pi≤C := by dsimp [C]; nlinarith only [mul_pos hCr Real.pi_pos]
  calc
    _ ≤ (2*Cr*Real.pi)*C₂*U^((a-1/2)*(1-r)+6*e*(2-r)+4*κ+η)+
        (6*Cg)*Cn*U^(2*R+2+η)/(1+V)^n+(E*Real.pi)*Cn*U^(2*R+2+η)/(1+V)^n := by
      exact add_le_add (add_le_add hc hj) ht
    _ = (2*Cr*Real.pi)*C₂*U^((a-1/2)*(1-r)+6*e*(2-r)+4*κ+η)+
        (6*Cg+E*Real.pi)*Cn*U^(2*R+2+η)/(1+V)^n := by ring
    _ ≤ _ := by gcongr

end SevenEighths.HeckeDyadic

end

end OAI

end Source719
