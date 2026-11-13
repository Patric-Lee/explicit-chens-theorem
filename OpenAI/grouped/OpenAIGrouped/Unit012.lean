import OpenAIGrouped.Unit011
import OpenAIGrouped.Unit009
import OpenAIGrouped.Unit007
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import OpenAIGrouped.Unit008
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/RayPrimeNormalizer.lean; sha256: 687d40a238d0963b8734a8a8c258fd32afc7c77fe8d66e06fe178c3802d4bebe -/
section Source480
namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Classical Topology ContDiff
namespace SevenEighths.RayPrimeNormalizer
open HeckeFamily
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

def normalizer (S : Finset (Ideal O)) (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  PNT.AnnularPrimeMass.weightedPrimeSumDeleted (RayQuotient.identityClass M H) S W x

include hH

theorem asymptotic (S : Finset (Ideal O)) (W : ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ => Real.log x / x ^ (1/6 : ℝ) * normalizer M H S W x)
      atTop (𝓝 ((RayQuotient.classNumber M H : ℝ)⁻¹ * ∫ y : ℝ, W y * y ^ (-5/6 : ℝ))) :=
  PNT.AnnularPrimeMass.weightedPrimeSumDeleted_tendsto _ S
    (HeckeRayPrimes.quotientClassCoeff_ratio_tendsto M H hH) W hW hc hp

theorem eventually_lower_bound (S : Finset (Ideal O)) (W : ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0)
    (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c * x ^ (1/6 : ℝ) / Real.log x ≤ normalizer M H S W x := by
  apply PNT.AnnularPrimeMass.weightedPrimeSumDeleted_eventually_lower_bound _ S
    (show 0 < (RayQuotient.classNumber M H : ℝ)⁻¹ from inv_pos.mpr (by
      exact_mod_cast RayQuotient.classNumber_pos M H))
    (HeckeRayPrimes.quotientClassCoeff_ratio_tendsto M H hH) W hW hc hp hW0 hWne

theorem eventually_pos (S : Finset (Ideal O)) (W : ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0)
    (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    ∀ᶠ x : ℝ in atTop, 0 < normalizer M H S W x := by
  apply PNT.AnnularPrimeMass.weightedPrimeSumDeleted_eventually_pos _ S
    (show 0 < (RayQuotient.classNumber M H : ℝ)⁻¹ from inv_pos.mpr (by
      exact_mod_cast RayQuotient.classNumber_pos M H))
    (HeckeRayPrimes.quotientClassCoeff_ratio_tendsto M H hH) W hW hc hp hW0 hWne

end SevenEighths.RayPrimeNormalizer

end

end OAI

end Source480

/- Original source: OAI/NumberTheory/DirichletL/Detector/PhysicalPoisson.lean; sha256: e11d050153c35e821df8372f14c29a250302bbb47ff95fb7cfbd56bee630818a -/
section Source481
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition ConcreteTraceCRT
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

lemma sexticGauss_frequency_congr (s : O) (hs : s≠0) (h k : O)
    (he : h-k ∈ (Ideal.span {s}:Ideal O)) : sexticGauss s hs h = sexticGauss s hs k := by
  have hmk := Ideal.Quotient.eq.mpr he
  simp only [sexticGauss, hmk]

def physicalQuotient (C : CalibrationData) (A s : O) (hs : s≠0)
    (m : O ⧸ Ideal.span {(C.generator*A)*s}) : ℂ :=
  calibratedNumerator C A (representative ((C.generator*A)*s) m) *
    sexticGauss s hs (-representative ((C.generator*A)*s) m)

lemma physicalQuotient_mk (C : CalibrationData) (A s : O) (hs : s≠0) (m : O) :
    physicalQuotient C A s hs (Ideal.Quotient.mk _ m) =
      calibratedNumerator C A m * sexticGauss s hs (-m) := by
  have hd : (C.generator*A)*s ∣ representative ((C.generator*A)*s) (Ideal.Quotient.mk _ m)-m :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (representative_spec _ _))
  have hA : representative ((C.generator*A)*s) (Ideal.Quotient.mk _ m)-m ∈
      (Ideal.span {C.generator*A}:Ideal O) :=
    Ideal.mem_span_singleton.mpr ((dvd_mul_right (C.generator*A) s).trans hd)
  have hs' : -representative ((C.generator*A)*s) (Ideal.Quotient.mk _ m)-(-m) ∈
      (Ideal.span {s}:Ideal O) := by
    apply Ideal.mem_span_singleton.mpr
    rw [show -representative ((C.generator*A)*s) (Ideal.Quotient.mk _ m)-(-m) =
      -(representative ((C.generator*A)*s) (Ideal.Quotient.mk _ m)-m) by ring]
    exact dvd_neg.mpr ((dvd_mul_left s (C.generator*A)).trans hd)
  unfold physicalQuotient
  rw [calibratedNumerator_congr C A _ m hA, sexticGauss_frequency_congr s hs _ (-m) hs']

theorem physical_row_poisson (C : CalibrationData) (A s : O) (hA : A≠0) (hs : s≠0)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W)
    (K : ℝ) (hK : 0<K) :
    (∑' m : O, calibratedNumerator C A m * sexticGauss s hs (-m) * W (elementNorm m/K)) =
      ((K / elementNorm (C.generator*A) : ℝ):ℂ) *
        ∑' H : O, actualCongruenceCoefficient C A s hA H *
          paperRadialFourier W (K*elementNorm H/elementNorm ((C.generator*A)*s)) := by
  let c := (C.generator*A)*s
  have hc : c≠0 := mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs
  let := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  have ht := actual_compact_radial_paper_poisson_trace W hWc hWs K hK c hc
    (physicalQuotient C A s hs)
  change (∑' m : O, physicalQuotient C A s hs (Ideal.Quotient.mk _ m) *
    W (‖eisEmbedding m‖^2/K)) =
    (K/‖eisEmbedding c‖^2:ℝ) • ∑' H : O,
      (∑ r : O ⧸ Ideal.span {c}, physicalQuotient C A s hs r *
        quotientTrace c hc (Ideal.Quotient.mk _ H*r)) *
        paperRadialFourier W (K*‖eisEmbedding H‖^2/‖eisEmbedding c‖^2) at ht
  have hf (H : O) : (∑ r : O ⧸ Ideal.span {c}, physicalQuotient C A s hs r *
      quotientTrace c hc (Ideal.Quotient.mk _ H*r)) =
        (Ideal.absNorm (Ideal.span {s}):ℂ) * actualCongruenceCoefficient C A s hA H := by
    rw [← actualPhysicalFourier_eq C A s hA hs H]
    exact (tsum_fintype _).symm
  simp_rw [physicalQuotient_mk, eisEmbedding_norm_sq_eq_absNorm_span, hf] at ht
  change (∑' m : O, calibratedNumerator C A m * sexticGauss s hs (-m) * W (elementNorm m/K)) =
    (K/elementNorm c:ℝ) • ∑' H : O,
      ((Ideal.absNorm (Ideal.span {s}):ℂ) * actualCongruenceCoefficient C A s hA H) *
        paperRadialFourier W (K*elementNorm H/elementNorm c) at ht
  rw [ht]
  simp only [mul_assoc, tsum_mul_left, Complex.real_smul, Complex.ofReal_div]
  have hn : (elementNorm s:ℂ)≠0 := by
    simp only [elementNorm, Complex.ofReal_natCast]
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hs)
  have hnorm : elementNorm c = elementNorm (C.generator*A) * elementNorm s := by
    dsimp only [elementNorm, c]
    rw [← Ideal.span_singleton_mul_span_singleton, map_mul, Nat.cast_mul]
  simp only [← mul_assoc C.generator A s]
  rw [hnorm, Complex.ofReal_mul]
  simp only [elementNorm, Complex.ofReal_natCast] at hn ⊢
  field_simp

end SevenEighths.ProbePhysical
end

end OAI

end Source481

/- Original source: OAI/NumberTheory/DirichletL/Detector/FrequencySupport.lean; sha256: b01983419b2fd94f976c056324f24e0b1571b6b93360c3775bc833da5ede4996 -/
section Source482
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition CanonicalRowCompletion
open CenteredMomentCommonSupport CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

def elementFourier (c : O) (hc : c≠0) (f : O → ℂ) (H : O) : ℂ :=
  ∑' x : Residue c, f (representative c x) * quotientTrace c hc (Ideal.Quotient.mk _ H*x)

lemma elementFourier_congr (c d : O) (hc : c≠0) (hd : d≠0) (f : O → ℂ) (H : O)
    (he : c=d) : elementFourier c hc f H = elementFourier d hd f H := by
  subst d
  rfl

def movingQuotient (A s : O) (hs : s≠0) (x : Residue (A*s)) : ℂ :=
  idealRowHom (representative (A*s) x) (Ideal.span {A}) *
    sexticGauss s hs (-representative (A*s) x)

lemma movingQuotient_mk (A s : O) (hs : s≠0) (m : O) :
    movingQuotient A s hs (Ideal.Quotient.mk _ m) =
      idealRowHom m (Ideal.span {A}) * sexticGauss s hs (-m) := by
  have hd : A*s ∣ representative (A*s) (Ideal.Quotient.mk _ m)-m :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (representative_spec _ _))
  have hA : representative (A*s) (Ideal.Quotient.mk _ m)-m ∈ (Ideal.span {A}:Ideal O) :=
    Ideal.mem_span_singleton.mpr ((dvd_mul_right A s).trans hd)
  have hs' : -representative (A*s) (Ideal.Quotient.mk _ m)-(-m) ∈ (Ideal.span {s}:Ideal O) := by
    apply Ideal.mem_span_singleton.mpr
    rw [show -representative (A*s) (Ideal.Quotient.mk _ m)-(-m) =
      -(representative (A*s) (Ideal.Quotient.mk _ m)-m) by ring]
    exact dvd_neg.mpr ((dvd_mul_left s A).trans hd)
  unfold movingQuotient
  rw [idealRowHom_congr_mod _ _ _ hA, sexticGauss_frequency_congr s hs _ (-m) hs']

lemma physicalFourier_eq_element (C : CalibrationData) (A s : O) (hA : A≠0) (hs : s≠0) (H : O) :
    actualPhysicalFourier C A s hA hs H =
      elementFourier (C.generator*(A*s)) (mul_ne_zero C.generator_ne_zero (mul_ne_zero hA hs))
        (fun m => C.residueMonoid m * idealRowHom m (Ideal.span {A}) * sexticGauss s hs (-m)) H := by
  change elementFourier ((C.generator*A)*s) (mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs)
    (fun m => C.residueMonoid m * idealRowHom m (Ideal.span {A}) * sexticGauss s hs (-m)) H = _
  apply elementFourier_congr
  exact mul_assoc _ _ _

lemma physicalFourier_eq_mixed (C : CalibrationData) (A s : O) (hA : A≠0) (hs : s≠0) (H : O) :
    actualPhysicalFourier C A s hA hs H =
      ∑' x : Residue (C.generator*(A*s)),
        C.residue (frequencyReduction C.generator (C.generator*(A*s)) (dvd_mul_right _ _) x) *
          movingQuotient A s hs (frequencyReduction (A*s) (C.generator*(A*s)) (dvd_mul_left _ _) x) *
          quotientTrace (C.generator*(A*s)) (mul_ne_zero C.generator_ne_zero (mul_ne_zero hA hs))
            (Ideal.Quotient.mk _ H*x) := by
  rw [physicalFourier_eq_element]
  unfold elementFourier
  apply tsum_congr
  intro x
  have he : Ideal.Quotient.mk (Ideal.span {C.generator*(A*s)})
      (representative (C.generator*(A*s)) x) = x := representative_spec _ _
  have hrA : frequencyReduction C.generator (C.generator*(A*s)) (dvd_mul_right _ _) x =
      Ideal.Quotient.mk _ (representative (C.generator*(A*s)) x) := by
    conv_lhs => rw [← he]
    rfl
  have hrB : frequencyReduction (A*s) (C.generator*(A*s)) (dvd_mul_left _ _) x =
      Ideal.Quotient.mk _ (representative (C.generator*(A*s)) x) := by
    conv_lhs => rw [← he]
    rfl
  rw [hrA, hrB, movingQuotient_mk]
  change _ = (C.residueMonoid _ * (_ * _)) * _

  ring

theorem actualPhysicalFourier_zero_off_calibration (S : Finset (Ideal O))
    (hS : ∀ P∈S, P.IsMaximal) (A s : O) (hA : A≠0) (hs : s≠0)
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O)
    (hH : ¬IsCoprime (calibrationForSet S hS).generator H) :
    actualPhysicalFourier (calibrationForSet S hS) A s hA hs H=0 := by
  rw [physicalFourier_eq_mixed]
  exact calibration_mixed_fourier_zero S hS (A*s) (mul_ne_zero hA hs) hcop (movingQuotient A s hs) H hH

theorem actualCongruenceCoefficient_zero_off_calibration (S : Finset (Ideal O))
    (hS : ∀ P∈S, P.IsMaximal) (A s : O) (hA : A≠0) (hs : s≠0)
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O)
    (hH : ¬IsCoprime (calibrationForSet S hS).generator H) :
    actualCongruenceCoefficient (calibrationForSet S hS) A s hA H=0 := by
  have he := actualPhysicalFourier_zero_off_calibration S hS A s hA hs hcop H hH
  rw [actualPhysicalFourier_eq] at he
  have hn : (Ideal.absNorm (Ideal.span {s}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hs)
  exact (mul_eq_zero.mp he).resolve_left hn

end SevenEighths.ProbePhysical
end

end OAI

end Source482

/- Original source: OAI/NumberTheory/DirichletL/Detector/SpectralSeparation.lean; sha256: ac9a787c061cb47ad79a18ceb178d2bc9275b89093ae0a1fe431fc9b9c8f347d -/
section Source483
namespace OAI

noncomputable section
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted
local notation "O" => ActualEisensteinCubic.O

def baseRowCoefficient (η : HeckeFamily.Character) (Xi : O →* ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) : O →* ℂ :=
  targetMonoid η * InitialMeanSquare.conjugateMonoid Xi * reciprocityPhaseMonoid s hs

lemma spectralSummand_mul_fixed_twist (S : Finset (Ideal O)) (D I J : Ideal O)
    (φ Ψ : O →* ℂ) (t : ℂ) :
    spectralSummand S D (φ*Ψ) t I J =
      φ (completedIndex I J) * spectralSummand S D Ψ t I J := by
  have hc (η : O →* ℂ) : cubeWeight η J =
      star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3 *
        η (primaryGenerator J)^3 / (Ideal.absNorm J:ℂ) := rfl
  unfold spectralSummand
  rw [hc, hc]
  simp only [columnWeight, MonoidHom.mul_apply, map_mul, map_pow, mul_pow, completedIndex]
  ring

theorem spectralSummand_row_separation (S : Finset (Ideal O)) (D I J : Ideal O)
    (η : HeckeFamily.Character) (Xi : O →* ℂ) (s : O)
    (hs : Supported (Ideal.span {s})) (m : O) (t : ℂ) :
    spectralSummand S D (rowCoefficient η Xi s hs m) t I J =
      idealRowHom m (Ideal.span {completedIndex I J}) *
        spectralSummand S D (baseRowCoefficient η Xi s hs) t I J := by
  have hr : rowCoefficient η Xi s hs m =
      ((idealRowHom m).toMonoidHom.comp principalIdealHom.toMonoidHom) *
        baseRowCoefficient η Xi s hs := by
    change _ * _ = _ * _
    exact mul_comm _ _
  rw [hr, spectralSummand_mul_fixed_twist]
  rfl

theorem calibrated_spectralSummand_separation (S : Finset (Ideal O)) (D I J : Ideal O)
    (η : HeckeFamily.Character) (C : ProbePhysical.CalibrationData) (s : O)
    (hs : Supported (Ideal.span {s})) (m : O) (t : ℂ) :
    C.residueMonoid m * spectralSummand S D (rowCoefficient η C.Xi s hs m) t I J =
      ProbePhysical.calibratedNumerator C (completedIndex I J) m *
        spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J := by
  rw [spectralSummand_row_separation]
  unfold ProbePhysical.calibratedNumerator
  ring

theorem spectralSummand_zero_completedIndex (S : Finset (Ideal O)) (D I J : Ideal O)
    (Ψ : O →* ℂ) (t : ℂ) (hz : completedIndex I J=0) :
    spectralSummand S D Ψ t I J=0 := by
  rcases mul_eq_zero.mp hz with hI | hJ
  · have hg : squarefreeGaussCoefficient I=0 := by
      unfold squarefreeGaussCoefficient
      rw [dite_eq_right (by simp [hI])]
    simp only [spectralSummand, columnWeight, hg, zero_mul, zero_div, mul_zero]
  · have hJ' : primaryGenerator J=0 := (pow_eq_zero_iff (by decide : 3≠0)).mp hJ
    have hc : cubeWeight Ψ J=0 := by
      change star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3 *
        Ψ (primaryGenerator J)^3 / (Ideal.absNorm J:ℂ)=0
      simp [hJ', FiniteGaussPhase.angularFactor]
    simp only [spectralSummand, hc, mul_zero, zero_mul]

end SevenEighths.ProbeRow
end

end OAI

end Source483

/- Original source: OAI/NumberTheory/DirichletL/Detector/RowAnalytic.lean; sha256: 0feee26f076e10767a3f7426fe13c89e56db7e60a8bb1e0dc73fb5684d609511 -/
section Source484
namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem fullIdealWeight_norm_eq_of_re (s t : ℂ) (h : s.re = t.re) (I : Ideal O) :
    ‖fullIdealWeight s I‖ = ‖fullIdealWeight t I‖ := by
  by_cases hI : I = 0
  · simp [hI, fullIdealWeight]
  · exact (norm_fullIdealWeight s ⟨I, hI⟩).trans
      ((by rw [h] : _ = _).trans (norm_fullIdealWeight t ⟨I, hI⟩).symm)

theorem fullIdealWeight_continuous (I : Ideal O) : Continuous (fun t => fullIdealWeight t I) := by
  by_cases hI : I = 0
  · simp only [hI, fullIdealWeight]
    exact continuous_const
  · have hn : (Ideal.absNorm I : ℂ) ≠ 0 := by
      exact_mod_cast (Ideal.absNorm_ne_zero_iff I).mpr
        (Ring.HasFiniteQuotients.finiteQuotient hI)
    simp only [fullIdealWeight, ite_eq_right hI]
    exact continuous_id.neg.const_cpow (Or.inl hn)

def rowMajorant (σ : ℝ) (p : Ideal O × Ideal O) : ℝ :=
  2 * (‖fullIdealWeight (σ : ℂ) p.1‖ * ‖fullIdealWeight (3 * (σ : ℂ)) p.2‖)

theorem rowMajorant_summable (σ : ℝ) (hσ : 1 < σ) : Summable (rowMajorant σ) := by
  have h3 : 1 < (3 * (σ : ℂ)).re := by norm_num; linarith
  exact ((fullIdealWeight_summable_norm (σ : ℂ) hσ).mul_of_nonneg
    (fullIdealWeight_summable_norm (3 * (σ : ℂ)) h3)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left 2

theorem spectralSummand_vertical_bound (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ y : ℝ) (p : Ideal O × Ideal O) :
    ‖spectralSummand S D Ψ ((σ : ℂ) + y * Complex.I) p.1 p.2‖ ≤ rowMajorant σ p := by
  have h1 : ((σ : ℂ) + y * Complex.I).re = (σ : ℂ).re := by simp
  have h3 : (3 * ((σ : ℂ) + y * Complex.I)).re = (3 * (σ : ℂ)).re := by simp
  simpa only [rowMajorant, fullIdealWeight_norm_eq_of_re _ _ h1,
    fullIdealWeight_norm_eq_of_re _ _ h3] using
    spectralSummand_norm_le S D Ψ hΨ ((σ : ℂ) + y * Complex.I) p.1 p.2

theorem spectralRow_continuous_vertical (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ) :
    Continuous (fun y : ℝ => spectralRow S D Ψ ((σ : ℂ) + y * Complex.I)) := by
  apply continuous_tsum _ (rowMajorant_summable σ hσ)
    (fun p y => spectralSummand_vertical_bound S D Ψ hΨ σ y p)
  intro p
  have hc : Continuous (fun y : ℝ => (σ : ℂ) + y * Complex.I) := by fun_prop
  exact continuous_const.mul ((fullIdealWeight_continuous p.1).comp hc |>.mul
    ((fullIdealWeight_continuous p.2).comp (continuous_const.mul hc)))

theorem spectralRow_vertical_bound (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ) (y : ℝ) :
    ‖spectralRow S D Ψ ((σ : ℂ) + y * Complex.I)‖ ≤ ∑' p, rowMajorant σ p := by
  have hs := spectralRow_summable S D Ψ hΨ ((σ : ℂ) + y * Complex.I) (by simpa using hσ)
  exact (norm_tsum_le_tsum_norm hs.norm).trans
    (hs.norm.tsum_le_tsum (fun p => spectralSummand_vertical_bound S D Ψ hΨ σ y p)
      (rowMajorant_summable σ hσ))

theorem verticalKernel_norm (Z : ℝ) (hZ : 0 < Z) (σ y : ℝ) :
    ‖(Z : ℂ) ^ ((σ : ℂ) + y * Complex.I) *
      Complex.exp (((σ : ℂ) + y * Complex.I) ^ 2)‖ =
      Z ^ σ * Real.exp (σ ^ 2) * Real.exp (-1 * y ^ 2) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hZ, Complex.norm_exp]
  have hre : (((σ : ℂ) + y * Complex.I) ^ 2).re = σ ^ 2 + (-1 * y ^ 2) := by
    simp [pow_two, Complex.mul_re, Complex.mul_im]
    ring
  rw [hre, Real.exp_add]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  ring

theorem spectralRow_vertical_integrable (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ)
    (Z : ℝ) (hZ : 0 < Z) :
    Integrable (fun y : ℝ => (Z : ℂ) ^ ((σ : ℂ) + y * Complex.I) *
      Complex.exp (((σ : ℂ) + y * Complex.I) ^ 2) *
      spectralRow S D Ψ ((σ : ℂ) + y * Complex.I)) := by
  let B : ℝ := ∑' p, rowMajorant σ p
  have hg := (integrable_exp_neg_mul_sq (b := 1) (by norm_num)).const_mul
    (Z ^ σ * Real.exp (σ ^ 2) * B)
  have hc : Continuous (fun y : ℝ => (σ : ℂ) + y * Complex.I) := by fun_prop
  have hk := (hc.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))).mul ((hc.pow 2).cexp)
  apply hg.mono' (hk.mul (spectralRow_continuous_vertical S D Ψ hΨ σ hσ)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro y
  dsimp only [Pi.mul_apply, Pi.pow_apply]
  rw [norm_mul, verticalKernel_norm Z hZ σ y]
  calc
    _ ≤ (Z ^ σ * Real.exp (σ ^ 2) * Real.exp (-1 * y ^ 2)) * B :=
      mul_le_mul_of_nonneg_left (spectralRow_vertical_bound S D Ψ hΨ σ hσ y)
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg hZ.le _) (Real.exp_pos _).le) (Real.exp_pos _).le)
    _ = _ := by ring

end SevenEighths.ProbeRow
end

end OAI

end Source484

/- Original source: OAI/NumberTheory/DirichletL/Detector/PhysicalAnalytic.lean; sha256: 2c333bbf6a0252156005ca3654c53172e3352d3776dcd01356a623fceaca3fd7 -/
section Source485
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ProbeRow CubicEisenstein CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem CalibrationData.residueMonoid_norm_le_one (C : CalibrationData) (a : O) :
    ‖C.residueMonoid a‖ ≤ 1 := by
  let : Finite (O ⧸ Ideal.span {C.generator}) :=
    ConcreteTraceCRT.finite_quotient_span C.generator_ne_zero
  let : Fintype (O ⧸ Ideal.span {C.generator}) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one C.residue (Ideal.Quotient.mk _ a)

theorem CalibrationData.Xi_norm_le_one (C : CalibrationData) (a : O) :
    ‖C.Xi a‖ ≤ 1 := by
  change ‖C.residueMonoid a * idealRowHom C.generator (Ideal.span {a})‖ ≤ 1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (C.residueMonoid_norm_le_one a)).trans
    (idealRowHom_norm _ _)

theorem CalibrationData.Xi_norm_one (C : CalibrationData) (a : O)
    (ha : Supported (Ideal.span {a})) (hcop : IsCoprime C.generator a) :
    ‖C.Xi a‖ = 1 := by
  let : Finite (O ⧸ Ideal.span {C.generator}) :=
    ConcreteTraceCRT.finite_quotient_span C.generator_ne_zero
  let : Fintype (O ⧸ Ideal.span {C.generator}) := Fintype.ofFinite _
  have hu := (CubicEisenstein.isUnit_quotient_span_iff C.generator a).mpr hcop
  have hξ : ‖C.residueMonoid a‖ = 1 := by
    exact (FiniteRayExpansion.norm_char_unit C.residue hu.unit)
  have hc : IsCoprime (Ideal.span {a} : Ideal O) (Ideal.span {C.generator}) :=
    (Ideal.isCoprime_span_singleton_iff a C.generator).mpr hcop.symm
  have h6 := idealRowHom_sixth_mask C.generator (Ideal.span {a}) ha
  rw [idealRowHom_argument_pow _ _ _ ha, ite_eq_left hc] at h6
  change ‖C.residueMonoid a * idealRowHom C.generator (Ideal.span {a})‖ = 1
  rw [norm_mul, hξ, Complex.norm_eq_one_of_pow_eq_one h6 (by decide : (6 : ℕ) ≠ 0), mul_one]

theorem calibrated_rowCoefficient_apply (η : HeckeFamily.Character) (C : CalibrationData)
    (s : O) (hs : Supported (Ideal.span {s})) (m a : O)
    (ha : Supported (Ideal.span {a})) (hcop : IsCoprime C.generator a) :
    rowCoefficient η C.Xi s hs m a = HeckeFamily.elementCoeff η a * (C.Xi a)⁻¹ *
      sexticReciprocityPhase a s * idealRowHom m (Ideal.span {a}) :=
  rowCoefficient_apply_unit η C.Xi s hs m a (C.Xi_norm_one a ha hcop)

theorem physicalRow_integrable (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (s : O) (hs : Supported (Ideal.span {s})) (m : O)
    (Z : ℝ) (hZ : 0 < Z) :
    Integrable (fun y : ℝ => (Z : ℂ) ^ ((4 : ℂ) + y * Complex.I) *
      Complex.exp (((4 : ℂ) + y * Complex.I) ^ 2) *
      spectralRow C.excluded D (rowCoefficient η C.Xi s hs m) ((4 : ℂ) + y * Complex.I)) := by
  exact spectralRow_vertical_integrable C.excluded D (rowCoefficient η C.Xi s hs m)
    (fun a => rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one s hs m a)
    4 (by norm_num) Z hZ

end SevenEighths.ProbePhysical
end

end OAI

end Source485

/- Original source: OAI/NumberTheory/DirichletL/Detector/Windows.lean; sha256: 58089460ec680f566d0d79bde77d495de6e98633b7a6ed230ae6cc035f977ba8 -/
section Source486
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem elementWindow_finite_support (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) :
    (Function.support (fun m : O => W (elementNorm m / R))).Finite := by
  obtain ⟨B, hB, hbound⟩ := compact_window_bound W hW
  obtain ⟨M, hM⟩ := exists_nat_gt (B * R)
  apply (ShortDraftLatticeCount.rowNormBall M).finite_toSet.subset
  intro m hm
  apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
  have hnorm : elementNorm m ≤ B * R := (div_le_iff₀ hR).mp (hbound _ hm)
  unfold elementNorm at hnorm
  exact_mod_cast hnorm.trans hM.le

theorem idealWindow_finite_support (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) :
    (Function.support (fun I : Ideal O => W ((Ideal.absNorm I : ℝ) / R))).Finite := by
  obtain ⟨B, hB, hbound⟩ := compact_window_bound W hW
  obtain ⟨M, hM⟩ := exists_nat_gt (B * R)
  apply (Ideal.finite_setOfPred_absNorm_le M).subset
  intro I hI
  have hnorm : (Ideal.absNorm I : ℝ) ≤ B * R := (div_le_iff₀ hR).mp (hbound _ hI)
  exact_mod_cast hnorm.trans hM.le

theorem elementWindow_mul_summable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) (F : O → ℂ) :
    Summable (fun m : O => W (elementNorm m / R) * F m) := by
  apply summable_of_hasFiniteSupport
  apply (elementWindow_finite_support W hW R hR).subset
  intro m hm hzero
  exact hm (by simp only [hzero, zero_mul])

theorem idealWindow_mul_summable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) (F : Ideal O → ℂ) :
    Summable (fun I : Ideal O => W ((Ideal.absNorm I : ℝ) / R) * F I) := by
  apply summable_of_hasFiniteSupport
  apply (idealWindow_finite_support W hW R hR).subset
  intro I hI hzero
  exact hI (by simp only [hzero, zero_mul])

end SevenEighths.ProbePhysical
end

end OAI

end Source486

/- Original source: OAI/NumberTheory/DirichletL/Detector/PhysicalReopen.lean; sha256: 17b2815b48db16c5534bda27e55a568e738290c5b4ce0ea24832c9e63287e376 -/
section Source487
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ProbeCompleted ProbeRow CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O

lemma supportedElement_ne_zero (s : O) (hs : Supported (Ideal.span {s})) : s≠0 := by
  intro h
  apply hs.1
  simp [h]

lemma finite_support_tsum_comm {α β : Type*} (f : α → β → ℂ) (S : Finset α)
    (hz : ∀ a, a∉S → ∀ b, f a b=0) (hs : ∀ a∈S, Summable (f a)) :
    (∑' a, ∑' b, f a b) = ∑' b, ∑' a, f a b := by
  calc
    _ = ∑ a∈S, ∑' b, f a b := tsum_eq_sum (fun a ha => by simp only [hz a ha, tsum_zero])
    _ = ∑' b, ∑ a∈S, f a b := (Summable.tsum_finsetSum hs).symm
    _ = _ := by
      apply tsum_congr
      intro b
      exact (tsum_eq_sum (fun a ha => hz a ha b)).symm

theorem physical_spectral_reopen (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D : Ideal O) (s : O)
    (hs : Supported (Ideal.span {s})) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (K : ℝ) (hK : 0<K) (t : ℂ) (ht : 1<t.re) :
    (∑' m : O, C.residueMonoid m * sexticGauss s (supportedElement_ne_zero s hs) (-m) *
      W (elementNorm m/K) * spectralRow S D (rowCoefficient η C.Xi s hs m) t) =
    ∑' p : Ideal O × Ideal O, spectralSummand S D (baseRowCoefficient η C.Xi s hs) t p.1 p.2 *
      ∑' m : O, calibratedNumerator C (completedIndex p.1 p.2) m *
        sexticGauss s (supportedElement_ne_zero s hs) (-m) * W (elementNorm m/K) := by
  let F (m : O) (p : Ideal O × Ideal O) : ℂ :=
    C.residueMonoid m * sexticGauss s (supportedElement_ne_zero s hs) (-m) * W (elementNorm m/K) *
      spectralSummand S D (rowCoefficient η C.Xi s hs m) t p.1 p.2
  have hfin := elementWindow_finite_support W hW K hK
  have hzero : ∀ m, m∉hfin.toFinset → ∀ p, F m p=0 := by
    intro m hm p
    have hz : W (elementNorm m/K)=0 := by simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using hm
    simp only [F, hz, mul_zero, zero_mul]
  have hsum (m : O) : Summable (F m) :=
    (spectralRow_summable S D (rowCoefficient η C.Xi s hs m)
      (rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one s hs m) t ht).mul_left _
  have he := finite_support_tsum_comm F hfin.toFinset hzero (fun m _ => hsum m)
  calc
    _ = ∑' m : O, ∑' p : Ideal O × Ideal O, F m p := by
      simp only [F, spectralRow, tsum_mul_left]
    _ = ∑' p : Ideal O × Ideal O, ∑' m : O, F m p := he
    _ = _ := by
      apply tsum_congr
      intro p
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      unfold F
      rw [spectralSummand_row_separation]
      unfold calibratedNumerator
      ring

end SevenEighths.ProbePhysical
end

end OAI

end Source487

/- Original source: OAI/NumberTheory/DirichletL/Detector/CalibrationRemoval.lean; sha256: 36cfd6b37ce7823c249e0f1e9535bd5ddc405e83a19d102f365b20757ef69fc8 -/
section Source488
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition CanonicalRowCompletion
open CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

lemma sexticGauss_unit_scale (s : O) (hs : Supported (Ideal.span {s}))
    (b h : O) (hcop : IsCoprime b s) :
    sexticGauss s (supportedElement_ne_zero s hs) (b*h) =
      (idealRowHom b (Ideal.span {s}))⁻¹ * sexticGauss s (supportedElement_ne_zero s hs) h := by
  let := finite_quotient_span (supportedElement_ne_zero s hs)
  let : Fintype (Residue s) := Fintype.ofFinite _
  let χ := supportedModulusCharacter s hs
  let ψ := quotientTrace s (supportedElement_ne_zero s hs)
  let u := residueUnit s b hcop.symm
  have he := gaussSum_mulShift_eq χ (ψ.mulShift (Ideal.Quotient.mk _ h)) u
  simp only [gaussSum, AddChar.mulShift_apply, MulChar.inv_apply_eq_inv', u, residueUnit_coe,
    χ, supportedModulusCharacter_mk] at he
  rw [← residueGauss_supported_mk s hs (b*h), ← residueGauss_supported_mk s hs h]
  simp only [residueGauss, tsum_fintype, map_mul]
  simpa only [ψ, mul_assoc, mul_comm, mul_left_comm] using he

lemma movingQuotient_unit_scale (A s : O) (hs : Supported (Ideal.span {s}))
    (b : O) (hcop : IsCoprime b s) (x : Residue (A*s)) :
    movingQuotient A s (supportedElement_ne_zero s hs) (Ideal.Quotient.mk _ b*x) =
      idealRowHom b (Ideal.span {A}) * (idealRowHom b (Ideal.span {s}))⁻¹ *
        movingQuotient A s (supportedElement_ne_zero s hs) x := by
  obtain ⟨m,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, movingQuotient_mk, movingQuotient_mk, idealRowHom_argument_mul]
  rw [show -(b*m)=b*(-m) by ring, sexticGauss_unit_scale s hs b (-m) hcop]
  ring

def barePhysicalFourier (A s : O) (hA : A≠0) (hs : s≠0) (H : O) : ℂ :=
  elementFourier (A*s) (mul_ne_zero hA hs)
    (fun m => idealRowHom m (Ideal.span {A}) * sexticGauss s hs (-m)) H

theorem actualPhysicalFourier_calibration_factor (S : Finset (Ideal O))
    (hS : ∀ P∈S, P.IsMaximal) (A s : O) (hA : A≠0)
    (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O) :
    let C := calibrationForSet S hS
    actualPhysicalFourier C A s hA (supportedElement_ne_zero s hs) H =
      (C.residueMonoid (A*s) * star (C.residueMonoid H) *
        (Real.sqrt (elementNorm C.generator):ℂ) * C.tau *
        idealRowHom C.generator (Ideal.span {A}) * (idealRowHom C.generator (Ideal.span {s}))⁻¹) *
      barePhysicalFourier A s hA (supportedElement_ne_zero s hs) H := by
  dsimp only
  let C := calibrationForSet S hS
  have hcs : IsCoprime C.generator s := hcop.of_mul_right_right
  rw [physicalFourier_eq_mixed, calibration_mixed_fourier S hS (A*s)
    (mul_ne_zero hA (supportedElement_ne_zero s hs)) hcop]
  dsimp only [C] at hcs ⊢
  simp_rw [movingQuotient_unit_scale A s hs (calibrationForSet S hS).generator hcs]
  simp only [mul_assoc, tsum_mul_left]
  rfl

def bareCongruenceCoefficient (A s : O) (hA : A≠0) (H : O) : ℂ :=
  congruenceCoefficient A s hA (outerQuotient A) (outerQuotient s) H

lemma barePhysicalFourier_eq (A s : O) (hA : A≠0) (hs : s≠0) (H : O) :
    barePhysicalFourier A s hA hs H =
      (Ideal.absNorm (Ideal.span {s}):ℂ)*bareCongruenceCoefficient A s hA H := by
  unfold bareCongruenceCoefficient
  rw [← fullFourier_eq_congruence A s hA hs]
  unfold barePhysicalFourier elementFourier fullFourier
  apply tsum_congr
  intro m
  rw [rawFourier_outer]
  have he : conductorReduction A s m = Ideal.Quotient.mk (Ideal.span {A}) (representative (A*s) m) := by
    conv_lhs => rw [← representative_spec (A*s) m]
    rfl
  rw [he]
  unfold outerQuotient
  rw [sexticGauss_coefficient_mk]

theorem actualCongruenceCoefficient_calibration_factor (S : Finset (Ideal O))
    (hS : ∀ P∈S, P.IsMaximal) (A s : O) (hA : A≠0)
    (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O) :
    let C := calibrationForSet S hS
    actualCongruenceCoefficient C A s hA H =
      (C.residueMonoid (A*s) * star (C.residueMonoid H) *
        (Real.sqrt (elementNorm C.generator):ℂ) * C.tau *
        idealRowHom C.generator (Ideal.span {A}) * (idealRowHom C.generator (Ideal.span {s}))⁻¹) *
      bareCongruenceCoefficient A s hA H := by
  dsimp only
  have he := actualPhysicalFourier_calibration_factor S hS A s hA hs hcop H
  dsimp only at he
  rw [actualPhysicalFourier_eq, barePhysicalFourier_eq] at he
  have hn : (Ideal.absNorm (Ideal.span {s}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (supportedElement_ne_zero s hs))
  apply mul_left_cancel₀ hn
  rw [he]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end Source488

/- Original source: OAI/NumberTheory/DirichletL/Detector/ScalarVanishing.lean; sha256: ddab9aa90212dcdea467bfda41e057184778c7e92323b0ddc64b3d1e54a0531f -/
section Source489
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition
local notation "O" => ActualEisensteinCubic.O

theorem higher_convolution_zero (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ ξ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n m : ℕ) (H : O) :
    (∑' d : O ⧸ Ideal.span {p^(m+2)},
      χ (Ideal.Quotient.mk _ (representative (p^(m+2)) d)) *
        primePowerGauss p hp.ne_zero ξ (n+(m+2))
          (H-p^(n+1)*representative (p^(m+2)) d)) = 0 := by
  let : Finite (O ⧸ Ideal.span {p^(m+2)}) :=
    ConcreteTraceCRT.finite_quotient_span (pow_ne_zero _ hp.ne_zero)
  let : Fintype (O ⧸ Ideal.span {p^(m+2)}) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {p*p^(n+(m+2))}) :=
    ConcreteTraceCRT.finite_quotient_span (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero))
  let : Fintype (O ⧸ Ideal.span {p*p^(n+(m+2))}) := Fintype.ofFinite _
  have hmod : p*p^(n+(m+2)) = p^(m+2)*p^(n+1) := by
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  have hinner (V : O) : (∑' d : O ⧸ Ideal.span {p^(m+2)},
      χ (Ideal.Quotient.mk _ (representative (p^(m+2)) d)) *
        quotientTrace (p^(m+2)) (pow_ne_zero _ hp.ne_zero)
          (Ideal.Quotient.mk _ ((-V)*representative (p^(m+2)) d))) =
      primePowerGauss p hp.ne_zero χ (m+1) (-V) := by
    change quotientFourier p (p^(m+2)) (pow_ne_zero _ hp.ne_zero) χ (-V) = _
    rw [primePowerGauss_eq_quotientFourier]
    apply quotientFourier_congr
    rw [← pow_succ']
  unfold primePowerGauss conductorFourier
  simp_rw [tsum_fintype, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro y hy
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
  change (∑ d : O ⧸ Ideal.span {p^(m+2)},
    χ (Ideal.Quotient.mk _ (representative (p^(m+2)) d)) *
      (ξ (Ideal.Quotient.mk _ v) *
        quotientTrace (p*p^(n+(m+2))) _
          (Ideal.Quotient.mk _ (H-p^(n+1)*representative (p^(m+2)) d)*Ideal.Quotient.mk _ v))) = 0
  have ht (d : O ⧸ Ideal.span {p^(m+2)}) :
      quotientTrace (p*p^(n+(m+2))) (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero))
        (Ideal.Quotient.mk _ ((H-p^(n+1)*representative (p^(m+2)) d)*v)) =
      quotientTrace (p*p^(n+(m+2))) (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero))
        (Ideal.Quotient.mk _ (H*v)) *
      quotientTrace (p^(m+2)) (pow_ne_zero _ hp.ne_zero)
        (Ideal.Quotient.mk _ ((-v)*representative (p^(m+2)) d)) := by
    have ht := quotientTrace_split_frequency (p^(m+2)) (p^(n+1))
      (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hp.ne_zero) H
      (representative (p^(m+2)) d) v
    simp only [quotientTrace_mk] at ht ⊢
    simpa only [← hmod] using ht
  simp_rw [← map_mul, ht]
  calc
    _ = ξ (Ideal.Quotient.mk _ v) *
        quotientTrace (p*p^(n+(m+2))) (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero))
          (Ideal.Quotient.mk _ (H*v)) *
        ∑ d : O ⧸ Ideal.span {p^(m+2)},
          χ (Ideal.Quotient.mk _ (representative (p^(m+2)) d)) *
            quotientTrace (p^(m+2)) (pow_ne_zero _ hp.ne_zero)
              (Ideal.Quotient.mk _ ((-v)*representative (p^(m+2)) d)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = quotientTrace (p*p^(n+(m+2))) (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero))
          (Ideal.Quotient.mk _ (H*v)) *
        (ξ (Ideal.Quotient.mk _ v) * primePowerGauss p hp.ne_zero χ (m+1) (-v)) := by
      have hi := hinner v
      rw [tsum_fintype] at hi
      rw [hi]
      ring
    _ = 0 := by rw [higher_outer_lift_annihilated p hp.ne_zero χ ξ (by omega : 0 < m+1) v, mul_zero]

theorem positiveScalar_kge_two (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n m j : ℕ) :
    positiveScalar p hp.ne_zero χ n (m+2) j = 0 := by
  rw [positiveScalar_full_lift p hp χ n (m+2) j (by omega),
    higher_convolution_zero p hp (χ^(m+2)) (χ^(n+1)) n m (p^j), mul_zero]

end SevenEighths.ProbePrimePower
end

end OAI

end Source489

/- Original source: OAI/NumberTheory/DirichletL/Detector/ScalarTable.lean; sha256: e7105589c7ab123f999440eb4a48c3c797f3004cdf82d64cdb5f158387a35a12 -/
section Source490
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

def gaussValuationTable (Q G : ℂ) (r n j : ℕ) : ℂ :=
  if 6 ∣ r then (if n+1 ≤ j then Q^(n+1) else 0) - (if n ≤ j then Q^n else 0)
  else if j=n then Q^n*G else 0

theorem actualSextic_gaussValuationTable (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (r n j : ℕ) :
    primePowerGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg ^ r) n (p^j) =
      gaussValuationTable (Ideal.absNorm (Ideal.span {p}))
        (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg ^ r) 1) r n j :=
  actualSextic_primePowerGauss_at_pow p hp hg hc r n j

theorem positiveScalar_actual_table (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (n k j : ℕ) :
    let χ := actualSextic (Ideal.span {p}) hg
    let Q : ℂ := Ideal.absNorm (Ideal.span {p})
    positiveScalar p hp.ne_zero χ n k j =
      if k=0 then gaussValuationTable Q (primeGauss p hp.ne_zero (χ^(n+1)) 1) (n+1) n j
      else if k=1 ∧ 1 ≤ j then
        (χ (-1))⁻¹ * primeGauss p hp.ne_zero χ 1 *
          gaussValuationTable Q (primeGauss p hp.ne_zero (χ^n) 1) n n (j-1)
      else 0 := by
  dsimp only
  rcases k with _ | k
  · rw [ite_eq_left rfl, positiveScalar_kzero, actualSextic_gaussValuationTable p hp hg hc]
  rcases k with _ | k
  · rcases j with _ | j
    · simp only [ zero_add, Nat.one_ne_zero, ite_false,
          show ¬(1:ℕ) ≤ 0 by omega, and_false]
      exact positiveScalar_kone_jzero p hp _ n
    · rw [ite_eq_right (by omega : (1:ℕ) ≠ 0), ite_eq_left ⟨rfl, by omega⟩,
        positiveScalar_kone p hp.ne_zero, MulChar.inv_apply_eq_inv',
        actualSextic_gaussValuationTable p hp hg hc]
      simp
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), positiveScalar_kge_two p hp]

theorem zero_index_scalar (p : O) (_hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (k j : ℕ) (_hk : k ≠ 0) :
    (χ^k) (Ideal.Quotient.mk _ (p^j)) = if j=0 then 1 else 0 := by
  by_cases hj : j=0
  · simp [hj]
  · rw [ite_eq_right hj]
    have hz : Ideal.Quotient.mk (Ideal.span {p}) (p^j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_pow_self p hj))
    rw [hz, MulChar.map_zero]

end SevenEighths.ProbePrimePower
end

end OAI

end Source490

/- Original source: OAI/NumberTheory/DirichletL/Detector/LocalPhysical.lean; sha256: 853242bc20a864a714dad73e8cb7c3077fa893fe19f0d4e322db0a381b0991a3 -/
section Source491
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalRowCompletion
open CubicEisenstein GaussianShiftedPartition ProbePrimePower ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma outerQuotient_prime_power (p : O) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (k : ℕ) (hk : k≠0) (d : O ⧸ Ideal.span {p^k}) :
    outerQuotient (p^k) d =
      (actualSextic (Ideal.span {p}) hg ^ k)
        (Ideal.Quotient.mk _ (representative (p^k) d)) := by
  unfold outerQuotient
  rw [← Ideal.span_singleton_pow, map_pow, idealRowHom_prime _ _ hg, MulChar.pow_apply' _ hk]

lemma sexticGauss_prime_power (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (n : ℕ) (H : O) :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) H =
      primePowerGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg^(n+1)) n H := by
  have he : sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) H =
      quotientFourier p (p^(n+1)) (pow_ne_zero _ hp.ne_zero)
        (actualSextic (Ideal.span {p}) hg^(n+1)) H := by
    unfold sexticGauss quotientFourier
    apply tsum_congr
    intro d
    have hc := outerQuotient_prime_power p hg (n+1) (by omega) d
    change idealRowHom (representative (p^(n+1)) d) (Ideal.span {p^(n+1)}) = _ at hc
    rw [hc]
    rw [(Ideal.Quotient.mk (Ideal.span {p^(n+1)})).map_mul, representative_spec]
  rw [he, primePowerGauss_eq_quotientFourier]
  apply quotientFourier_congr
  exact pow_succ' p n

theorem bareCongruenceCoefficient_prime_power_pos (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (n k j : ℕ) (hk : k≠0) :
    bareCongruenceCoefficient (p^(n+1)) (p^k) (pow_ne_zero _ hp.ne_zero) (p^j) =
      positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j := by
  unfold bareCongruenceCoefficient congruenceCoefficient
  rw [positiveScalar, ite_eq_right hk]
  apply tsum_congr
  intro d
  rw [outerQuotient_prime_power p hg k hk]
  split_ifs with hd
  · rw [rawFourier_outer, sexticGauss_prime_power p hp hg]
  · ring

lemma sexticGauss_one (H : O) : sexticGauss 1 one_ne_zero H=1 := by
  let : Subsingleton (O ⧸ Ideal.span {(1:O)}) := by
    rw [Ideal.span_singleton_one]
    infer_instance
  let : Unique (O ⧸ Ideal.span {(1:O)}) := uniqueOfSubsingleton 0
  let : Fintype (O ⧸ Ideal.span {(1:O)}) := Fintype.ofFinite _
  unfold sexticGauss
  have hrow (d : O ⧸ Ideal.span {(1:O)}) :
      idealRowHom (representative 1 d) (Ideal.span {(1:O)})=1 := by
    rw [Ideal.span_singleton_one, ← Ideal.one_eq_top, map_one]
  simp only [hrow, one_mul]
  have ht (d : O ⧸ Ideal.span {(1:O)}) :
      quotientTrace 1 one_ne_zero (Ideal.Quotient.mk _ H*d)=1 := by
    rw [Subsingleton.elim (Ideal.Quotient.mk _ H*d) 0, AddChar.map_zero_eq_one]
  simp only [ht, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_unique, one_smul]

lemma barePhysicalFourier_outer_one (A : O) (hA : A≠0) (H : O) :
    barePhysicalFourier A 1 hA one_ne_zero H = sexticGauss A hA H := by
  unfold barePhysicalFourier
  rw [elementFourier_congr (A*1) A (mul_ne_zero hA one_ne_zero) hA _ H (mul_one A)]
  simp only [sexticGauss_one, mul_one]
  rfl

lemma bareCongruenceCoefficient_outer_one (A : O) (hA : A≠0) (H : O) :
    bareCongruenceCoefficient A 1 hA H=sexticGauss A hA H := by
  have he := barePhysicalFourier_eq A 1 hA one_ne_zero H
  rw [barePhysicalFourier_outer_one] at he
  simpa only [Ideal.span_singleton_one, ← Ideal.one_eq_top, map_one, Nat.cast_one, one_mul] using he.symm

theorem bareCongruenceCoefficient_prime_power (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p}) (n k j : ℕ) :
    bareCongruenceCoefficient (p^(n+1)) (p^k) (pow_ne_zero _ hp.ne_zero) (p^j) =
      positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j := by
  by_cases hk : k=0
  · subst k
    rw [pow_zero, bareCongruenceCoefficient_outer_one, sexticGauss_prime_power p hp hg,
      positiveScalar_kzero]
  · exact bareCongruenceCoefficient_prime_power_pos p hp hg n k j hk

theorem bareCongruenceCoefficient_inner_one (s : O) (hs : s≠0) (H : O) :
    bareCongruenceCoefficient 1 s one_ne_zero H = outerQuotient s (Ideal.Quotient.mk _ H) := by
  let := finite_quotient_span hs
  let : Fintype (O ⧸ Ideal.span {s}) := Fintype.ofFinite _
  have htest (d : O ⧸ Ideal.span {s}) :
      s∣H-1*representative s d ↔ d=Ideal.Quotient.mk _ H := by
    rw [one_mul, ← Ideal.mem_span_singleton, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem,
      representative_spec, eq_comm]
  have hraw (k : O) : rawFourier 1 one_ne_zero (outerQuotient 1) k=1 := by
    rw [rawFourier_outer, sexticGauss_one]
  unfold bareCongruenceCoefficient congruenceCoefficient
  simp_rw [hraw]
  simp only [tsum_fintype]
  rw [Finset.sum_eq_single (Ideal.Quotient.mk _ H)]
  · rw [dite_eq_left ((htest _).mpr rfl), mul_one]
  · intro d hd hne
    rw [dite_eq_right ((htest d).not.mpr hne), mul_zero]
  · simp

end SevenEighths.ProbePhysical
end

end OAI

end Source491

/- Original source: OAI/NumberTheory/DirichletL/Detector/PhysicalCRT.lean; sha256: d9b9c31ec2acfaddd4bca0fc2475151c9947851b39b27eb7f7721a77c98557a3 -/
section Source492
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CanonicalRowCompletion GaussianShiftedPartition
open CanonicalQuadraticSieve CenteredMomentCorrelation CenteredMomentCommonSupport
open CenteredMomentFourier CenteredMomentFirstPoisson CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

theorem coprime_function_fourier (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a * b))]
    (Fa : Residue a → ℂ) (F : Residue b → ℂ)
    (h : Residue (a * b)) :
    (∑ x : Residue (a * b),
      Fa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        F (frequencyReduction b (a * b) (dvd_mul_left b a) x) *
          quotientTrace (a * b) (mul_ne_zero ha hb) (h * x)) =
      (∑ x : Residue a, Fa (Ideal.Quotient.mk _ b*x) *
        quotientTrace a ha (frequencyReduction a (a*b) (dvd_mul_right a b) h*x)) *
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
  simp only [ he, mul_add, AddChar.map_add_eq_mul,
    quotientTrace_scaled a b (a * b) rfl ha hb (mul_ne_zero ha hb),
    quotientTrace_scaled b a (a * b) (mul_comm a b) hb ha (mul_ne_zero ha hb)]
  simp only [Fintype.sum_prod_type, ]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem sexticGauss_coprime_product (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hcop : IsCoprime a b) (H : O) :
    sexticGauss (a*b) (mul_ne_zero (supportedElement_ne_zero a ha) (supportedElement_ne_zero b hb)) H =
      idealRowHom b (Ideal.span {a}) * idealRowHom a (Ideal.span {b}) *
        sexticGauss a (supportedElement_ne_zero a ha) H *
        sexticGauss b (supportedElement_ne_zero b hb) H := by
  let := finite_quotient_span (supportedElement_ne_zero a ha)
  let := finite_quotient_span (supportedElement_ne_zero b hb)
  let := finite_quotient_span (mul_ne_zero (supportedElement_ne_zero a ha) (supportedElement_ne_zero b hb))
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (a*b)) := Fintype.ofFinite _
  have he := coprime_character_fourier a b (supportedElement_ne_zero a ha) (supportedElement_ne_zero b hb)
    hcop (supportedModulusCharacter a ha) (supportedModulusCharacter b hb) (Ideal.Quotient.mk _ H)
  simp only [frequencyReduction_mk, supportedModulusCharacter_mk,
    residueGauss_supported_mk] at he
  rw [← he]
  unfold sexticGauss
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨m,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [sexticGauss_coefficient_mk]
  simp only [frequencyReduction_mk, supportedModulusCharacter_mk]
  congr 1
  rw [← Ideal.span_singleton_mul_span_singleton, map_mul]

lemma elementFourier_const_mul (c : O) (hc : c≠0) (F : O → ℂ) (H : O) (B : ℂ) :
    elementFourier c hc (fun m => B*F m) H = B*elementFourier c hc F H := by
  simp only [elementFourier, mul_assoc, tsum_mul_left]

lemma bareMoving_product (A B s r : O) (hs : Supported (Ideal.span {s}))
    (hr : Supported (Ideal.span {r})) (hcop : IsCoprime s r) (m : O) :
    idealRowHom m (Ideal.span {A*B}) *
      sexticGauss (s*r) (mul_ne_zero (supportedElement_ne_zero s hs) (supportedElement_ne_zero r hr)) (-m) =
    (idealRowHom r (Ideal.span {s}) * idealRowHom s (Ideal.span {r})) *
      ((idealRowHom m (Ideal.span {A}) * sexticGauss s (supportedElement_ne_zero s hs) (-m)) *
        (idealRowHom m (Ideal.span {B}) * sexticGauss r (supportedElement_ne_zero r hr) (-m))) := by
  rw [sexticGauss_coprime_product s r hs hr hcop]
  rw [← Ideal.span_singleton_mul_span_singleton, map_mul]
  ring

theorem barePhysicalFourier_product (A B s r : O) (hA : A≠0) (hB : B≠0)
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hcop : IsCoprime (A*s) (B*r)) (H : O) :
    barePhysicalFourier (A*B) (s*r) (mul_ne_zero hA hB)
      (mul_ne_zero (supportedElement_ne_zero s hs) (supportedElement_ne_zero r hr)) H =
    (idealRowHom r (Ideal.span {s}) * idealRowHom s (Ideal.span {r})) *
      (idealRowHom (B*r) (Ideal.span {A}) * (idealRowHom (B*r) (Ideal.span {s}))⁻¹) *
      (idealRowHom (A*s) (Ideal.span {B}) * (idealRowHom (A*s) (Ideal.span {r}))⁻¹) *
      barePhysicalFourier A s hA (supportedElement_ne_zero s hs) H *
      barePhysicalFourier B r hB (supportedElement_ne_zero r hr) H := by
  have hsc : IsCoprime s r := hcop.of_mul_left_right.of_mul_right_right
  have hc1 : IsCoprime (B*r) s := hcop.of_mul_left_right.symm
  have hc2 : IsCoprime (A*s) r := hcop.of_mul_right_right
  have hAs := mul_ne_zero hA (supportedElement_ne_zero s hs)
  have hBr := mul_ne_zero hB (supportedElement_ne_zero r hr)
  let := finite_quotient_span hAs
  let := finite_quotient_span hBr
  let := finite_quotient_span (mul_ne_zero hAs hBr)
  let : Fintype (Residue (A*s)) := Fintype.ofFinite _
  let : Fintype (Residue (B*r)) := Fintype.ofFinite _
  let : Fintype (Residue ((A*s)*(B*r))) := Fintype.ofFinite _
  have he := coprime_function_fourier (A*s) (B*r) hAs hBr hcop
    (movingQuotient A s (supportedElement_ne_zero s hs))
    (movingQuotient B r (supportedElement_ne_zero r hr)) (Ideal.Quotient.mk _ H)
  simp only [frequencyReduction_mk] at he
  simp_rw [movingQuotient_unit_scale A s hs (B*r) hc1,
    movingQuotient_unit_scale B r hr (A*s) hc2, mul_assoc] at he
  simp only [← Finset.mul_sum] at he
  have hexpand : elementFourier ((A*s)*(B*r)) (mul_ne_zero hAs hBr)
      (fun m => (idealRowHom m (Ideal.span {A}) * sexticGauss s (supportedElement_ne_zero s hs) (-m)) *
        (idealRowHom m (Ideal.span {B}) * sexticGauss r (supportedElement_ne_zero r hr) (-m))) H =
      (idealRowHom (B*r) (Ideal.span {A}) * (idealRowHom (B*r) (Ideal.span {s}))⁻¹) *
      (idealRowHom (A*s) (Ideal.span {B}) * (idealRowHom (A*s) (Ideal.span {r}))⁻¹) *
      barePhysicalFourier A s hA (supportedElement_ne_zero s hs) H *
      barePhysicalFourier B r hB (supportedElement_ne_zero r hr) H := by
    unfold elementFourier
    rw [tsum_fintype]
    calc
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        have hmk := representative_spec ((A*s)*(B*r)) x
        have hred1 : frequencyReduction (A*s) ((A*s)*(B*r)) (dvd_mul_right _ _) x =
            Ideal.Quotient.mk _ (representative ((A*s)*(B*r)) x) := by
          conv_lhs => rw [← hmk]
          rfl
        have hred2 : frequencyReduction (B*r) ((A*s)*(B*r)) (dvd_mul_left _ _) x =
            Ideal.Quotient.mk _ (representative ((A*s)*(B*r)) x) := by
          conv_lhs => rw [← hmk]
          rfl
        rw [hred1, hred2, movingQuotient_mk, movingQuotient_mk]
        ring
      _ = _ := he
      _ = _ := by
        simp only [barePhysicalFourier, elementFourier, movingQuotient, tsum_fintype]
        ring
  simp only [barePhysicalFourier] at hexpand
  unfold barePhysicalFourier
  rw [elementFourier_congr ((A*B)*(s*r)) ((A*s)*(B*r)) _ (mul_ne_zero hAs hBr) _ H (by ring)]
  simp_rw [bareMoving_product A B s r hs hr hsc]
  rw [elementFourier_const_mul, hexpand]
  ring

theorem bareCongruenceCoefficient_product (A B s r : O) (hA : A≠0) (hB : B≠0)
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hcop : IsCoprime (A*s) (B*r)) (H : O) :
    bareCongruenceCoefficient (A*B) (s*r) (mul_ne_zero hA hB) H =
    (idealRowHom r (Ideal.span {s}) * idealRowHom s (Ideal.span {r})) *
      (idealRowHom (B*r) (Ideal.span {A}) * (idealRowHom (B*r) (Ideal.span {s}))⁻¹) *
      (idealRowHom (A*s) (Ideal.span {B}) * (idealRowHom (A*s) (Ideal.span {r}))⁻¹) *
      bareCongruenceCoefficient A s hA H * bareCongruenceCoefficient B r hB H := by
  have he := barePhysicalFourier_product A B s r hA hB hs hr hcop H
  simp only [barePhysicalFourier_eq] at he
  have hnorm : Ideal.absNorm (Ideal.span {s*r}) =
      Ideal.absNorm (Ideal.span {s}) * Ideal.absNorm (Ideal.span {r}) := by
    rw [← Ideal.span_singleton_mul_span_singleton, map_mul]
  rw [hnorm, Nat.cast_mul] at he
  have hns : (Ideal.absNorm (Ideal.span {s}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (supportedElement_ne_zero s hs))
  have hnr : (Ideal.absNorm (Ideal.span {r}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (supportedElement_ne_zero r hr))
  apply mul_left_cancel₀ (mul_ne_zero hns hnr)
  rw [he]
  ring

lemma idealRowHom_ne_zero_of_coprime (s a : O)
    (hs : Supported (Ideal.span {s})) (hc : IsCoprime s a) :
    idealRowHom a (Ideal.span {s})≠0 := by
  rw [← supportedModulusCharacter_mk s hs a]
  exact (supportedModulusCharacter s hs).apply_ne_zero_iff.mpr
    ((isUnit_quotient_span_iff s a).mpr hc)

theorem bareCongruenceCoefficient_product_reduced (A B s r : O) (hA : A≠0) (hB : B≠0)
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hcop : IsCoprime (A*s) (B*r)) (H : O) :
    bareCongruenceCoefficient (A*B) (s*r) (mul_ne_zero hA hB) H =
      (idealRowHom B (Ideal.span {A}) * idealRowHom r (Ideal.span {A}) *
       idealRowHom A (Ideal.span {B}) * idealRowHom s (Ideal.span {B})) /
      (idealRowHom B (Ideal.span {s}) * idealRowHom A (Ideal.span {r})) *
      bareCongruenceCoefficient A s hA H * bareCongruenceCoefficient B r hB H := by
  rw [bareCongruenceCoefficient_product A B s r hA hB hs hr hcop H]
  have hsr := idealRowHom_ne_zero_of_coprime s r hs
    hcop.of_mul_left_right.of_mul_right_right
  have hrs := idealRowHom_ne_zero_of_coprime r s hr
    hcop.of_mul_left_right.of_mul_right_right.symm
  have hsB := idealRowHom_ne_zero_of_coprime s B hs
    hcop.of_mul_left_right.of_mul_right_left
  have hrA := idealRowHom_ne_zero_of_coprime r A hr
    hcop.of_mul_left_left.of_mul_right_right.symm
  simp only [idealRowHom_argument_mul]
  field_simp

end SevenEighths.ProbePhysical
end

end OAI

end Source492

/- Original source: OAI/NumberTheory/DirichletL/Detector/PhaseCancellation.lean; sha256: ee63346ce2709592091877618f6a15e913bddae5c7c5666720c965491b3be79f -/
section Source493
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates QuadraticGaussRay ConcreteTraceCRT
open QuadraticAllOddCRT CanonicalRowCompletion CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem quadraticRayValue_norm_one (r : EisensteinEPrimaryPhase.Coord)
    (hr : EisensteinEPrimaryPhase.odd r) : ‖quadraticRayValue r‖ = 1 := by
  rw [quadraticRayValue_eq_fourthRoot r hr]
  simp [fourthRoot]

theorem G_norm_one (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hu : IsUnit (Ideal.Quotient.mk cubicTwoIdeal a)) : ‖G a‖ = 1 := by
  have hχ := congrArg
    (fun η : MulChar (O ⧸ cubicTwoIdeal) O => η (Ideal.Quotient.mk cubicTwoIdeal a))
    (cubicChar_pow_three cubicTwoIdeal cubicTwoIdeal_good)
  simp only [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), MulChar.one_apply hu] at hχ
  have hc := congrArg eisEmbedding hχ
  simp only [map_pow, map_one] at hc
  have hn := Complex.norm_eq_one_of_pow_eq_one hc (by decide : (3 : ℕ) ≠ 0)
  change ‖fixedGValue (residue a)‖ = 1
  simp only [fixedGValue, ← fixed_two_mk_eq_residue_lift, norm_mul, norm_inv,
    hn, inv_one, one_mul]
  exact quadraticRayValue_norm_one _ ha

theorem cubicTwo_isUnit_of_odd (a : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a)) :
    IsUnit (Ideal.Quotient.mk cubicTwoIdeal a) := by
  let : Field (O ⧸ cubicTwoIdeal) := Ideal.Quotient.field _
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hd : (2 : O) ∣ a := by
    simpa only [cubicTwoIdeal, Ideal.mem_span_singleton, neg_dvd] using hm
  exact ((odd_residue_iff_not_two_dvd a).mp ha) hd

theorem G_norm_one_of_odd (a : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a)) : ‖G a‖ = 1 :=
  G_norm_one a ha (cubicTwo_isUnit_of_odd a ha)

theorem G_conjugate_cancel (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hu : IsUnit (Ideal.Quotient.mk cubicTwoIdeal a)) : star (G a) * G a = 1 := by
  have hn := G_norm_one a ha hu
  have hs : star (G a) = (G a)⁻¹ := (Complex.inv_eq_conj hn).symm
  rw [hs]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mp (by rw [hn]; norm_num))

theorem completed_phase_cancel (c n : O)
    (hc : EisensteinEPrimaryPhase.odd (residue c))
    (hn : EisensteinEPrimaryPhase.odd (residue n))
    (hu : IsUnit (Ideal.Quotient.mk cubicTwoIdeal (c * n ^ 3))) :
    star (G (c * n ^ 3)) * (G c * reciprocitySign c n * G (n ^ 3)) = 1 := by
  rw [← G_completed_index c n hc hn]
  apply G_conjugate_cancel _ _ hu
  rw [show c * n ^ 3 = c * ((n * n) * n) by ring]
  simp only [residue_mul]
  exact odd_mul _ _ hc (odd_mul _ _ (odd_mul _ _ hn hn) hn)

end SevenEighths.ProbePhase
end

end OAI

end Source493

/- Original source: OAI/NumberTheory/DirichletL/Detector/PrimePhase.lean; sha256: 3f653e31f6fc9597c004a2337ff2c176aeba478ffb2e0460c238355506cc1b1c -/
section Source494
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge QuadraticGaussRay FiniteGaussPhase CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem normalizedTraceGauss_eq_normalizedGauss (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) :
    letI : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
    letI : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
    ConcreteBreveE.normalizedTraceGauss p hp χ =
      ProbeGauss.normalizedGauss χ (quotientTrace p hp) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hn : Real.sqrt (Nat.card (O ⧸ Ideal.span {p}) : ℝ) = ‖eisEmbedding p‖ := by
    change Real.sqrt (Ideal.absNorm (Ideal.span {p}) : ℝ) = _
    rw [← eisEmbedding_norm_sq_eq_absNorm_span, Real.sqrt_sq (norm_nonneg _)]
  simp only [ConcreteBreveE.normalizedTraceGauss, ProbeGauss.normalizedGauss,
    quotientTrace, ← Nat.card_eq_fintype_card, hn]

theorem quadraticRayValue_eq_normalizedTraceGauss (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    quadraticRayValue (residue p) =
      ConcreteBreveE.normalizedTraceGauss p hp (actualSextic (Ideal.span {p}) hg ^ 3) := by
  let pp : Unit → O := fun _ => p
  have hpp : ∀ i, pp i ≠ 0 := fun _ => hp
  have hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {pp i})) := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have he := canonicalProductGauss_three_eq_rayValue pp hpp hcop (fun _ => hg) (fun _ => hc)
  rw [canonicalProductGauss_cross_factors pp hpp hcop (fun _ => hg) (fun _ => 3)] at he
  simpa [pp] using he.symm

theorem G_cube_eq_normalizedTraceGauss (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (ho : EisensteinEPrimaryPhase.odd (residue p)) :
    G (p ^ 3) =
      ConcreteBreveE.normalizedTraceGauss p hp (actualSextic (Ideal.span {p}) hg ^ 3) := by
  rw [G_cube p ho (cubicTwo_isUnit_of_odd p ho)]
  exact quadraticRayValue_eq_normalizedTraceGauss p hp hg hc

theorem normalizedTraceGauss_three_sq (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    ConcreteBreveE.normalizedTraceGauss p hp (actualSextic (Ideal.span {p}) hg ^ 3) ^ 2 =
      actualSextic (Ideal.span {p}) hg (-1) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  let χ := actualSextic (Ideal.span {p}) hg
  have h6 : χ ^ 6 = 1 := (ProbePrimePower.actualSextic_pow_eq_one_iff _ hg hc 6).mpr (by decide)
  have h3 : χ ^ 3 ≠ 1 := fun h => (by decide : ¬6 ∣ 3)
    ((ProbePrimePower.actualSextic_pow_eq_one_iff _ hg hc 3).mp h)
  have hi : (χ ^ 3)⁻¹ = χ ^ 3 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add]
    exact h6
  have hψ : (quotientTrace p hp).IsPrimitive :=
    GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp
  have he := ProbeGauss.normalizedGauss_inverse_pair (χ ^ 3) (quotientTrace p hp) h3 hψ
  rw [hi, ← pow_two] at he
  rw [normalizedTraceGauss_eq_normalizedGauss]
  rw [he]
  simp only [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), ← map_pow]
  norm_num
  rfl

theorem reciprocitySign_self_eq_sextic_neg_one (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (ho : EisensteinEPrimaryPhase.odd (residue p)) :
    reciprocitySign p p = actualSextic (Ideal.span {p}) hg (-1) := by
  have hq := QuadraticAllOddCRT.quadraticRayValue_mul (residue p) (residue p) ho ho
  rw [quadraticRayValue_square _ ho] at hq
  have hprod : reciprocitySign p p * quadraticRayValue (residue p) ^ 2 = 1 := by
    simpa only [reciprocitySign, pow_two, mul_assoc] using hq.symm
  have he := normalizedTraceGauss_three_sq p hp hg hc
  rw [← quadraticRayValue_eq_normalizedTraceGauss p hp hg hc] at he
  rw [he] at hprod
  calc
    reciprocitySign p p = reciprocitySign p p * 1 := (mul_one _).symm
    _ = reciprocitySign p p * (reciprocitySign p p * actualSextic (Ideal.span {p}) hg (-1)) := by rw [hprod]
    _ = reciprocitySign p p ^ 2 * actualSextic (Ideal.span {p}) hg (-1) := by ring
    _ = _ := by rw [reciprocitySign_sq p p ho ho, one_mul]

end SevenEighths.ProbePhase
end

end OAI

end Source494

/- Original source: OAI/NumberTheory/DirichletL/Detector/PhasePowers.lean; sha256: 4b1a6b0e346f9ebbbbe7786ffadae868931b4d504301a6203729832ab6cb54a3 -/
section Source495
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates QuadraticGaussRay QuadraticAllOddCRT
local notation "O" => ActualEisensteinCubic.O

lemma residue_one_mod_four : residue (1 : O) = (1, 0) := by
  have he : (1 : O) = eval 1 0 := by simp [eval]
  rw [he, residue_eval]
  norm_num

lemma odd_residue_one : EisensteinEPrimaryPhase.odd (residue (1 : O)) := by
  rw [residue_one_mod_four]
  decide

lemma odd_residue_pow (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a)) (n : ℕ) :
    EisensteinEPrimaryPhase.odd (residue (a ^ n)) := by
  induction n with
  | zero => simpa only [pow_zero] using odd_residue_one
  | succ n ih =>
    rw [pow_succ, residue_mul]
    exact odd_mul _ _ ih ha

lemma reciprocitySign_symm (a b : O) : reciprocitySign a b = reciprocitySign b a := by
  simp only [reciprocitySign, quadraticRaySign_symm]

lemma reciprocitySign_one_left (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a)) :
    reciprocitySign 1 a = 1 := by
  have ht : ∀ r : EisensteinEPrimaryPhase.Coord, EisensteinEPrimaryPhase.odd r →
      quadraticRaySign (1, 0) r = 1 := by decide
  unfold reciprocitySign
  rw [residue_one_mod_four]
  exact_mod_cast ht (residue a) ha

lemma reciprocitySign_mul_left (a b c : O) :
    reciprocitySign (a * b) c = reciprocitySign a c * reciprocitySign b c := by
  simp only [reciprocitySign, residue_mul, quadraticRaySign_mul_left, Int.cast_mul]

lemma reciprocitySign_pow_left (a b : O)
    (hb : EisensteinEPrimaryPhase.odd (residue b)) (n : ℕ) :
    reciprocitySign (a ^ n) b = reciprocitySign a b ^ n := by
  induction n with
  | zero => simp only [pow_zero, reciprocitySign_one_left b hb]
  | succ n ih => rw [pow_succ, reciprocitySign_mul_left, ih, pow_succ]

lemma reciprocitySign_pow_right (a b : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a)) (n : ℕ) :
    reciprocitySign a (b ^ n) = reciprocitySign a b ^ n := by
  rw [reciprocitySign_symm, reciprocitySign_pow_left b a ha n, reciprocitySign_symm b a]

lemma G_one : G (1 : O) = 1 := by
  have hq : quadraticRayValue (residue (1 : O)) = 1 := by
    rw [residue_one_mod_four]
    change breveGaussianFourTerms 1 0 = 1
    rw [breveGaussianFourTerms_formula]
    norm_num
  have he := G_cube (1 : O) odd_residue_one (cubicTwo_isUnit_of_odd 1 odd_residue_one)
  simpa only [one_pow, hq] using he

theorem G_pow (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a)) (n : ℕ) :
    G (a ^ n) = G a ^ n * reciprocitySign a a ^ (n.choose 2) := by
  induction n with
  | zero => simp [G_one]
  | succ n ih =>
    rw [pow_succ, G_mul (a ^ n) a (odd_residue_pow a ha n) ha, ih,
      reciprocitySign_pow_left a a ha n, Nat.choose_succ_succ, Nat.choose_one_right,
      pow_add, pow_succ]
    ring

theorem reciprocitySign_cube_self (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a)) :
    reciprocitySign (a ^ 3) (a ^ 3) = reciprocitySign a a := by
  rw [reciprocitySign_cube_right (a ^ 3) a (odd_residue_pow a ha 3) ha,
    reciprocitySign_symm, reciprocitySign_cube_right a a ha ha]

theorem G_cube_power (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a)) (l : ℕ) :
    G (a ^ (3 * l)) = G (a ^ 3) ^ l * reciprocitySign a a ^ (l.choose 2) := by
  rw [pow_mul, G_pow (a ^ 3) (odd_residue_pow a ha 3), reciprocitySign_cube_self a ha]

theorem G_completed_prime_power (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a))
    (e l : ℕ) (he : e ≤ 1) :
    G (a ^ (e + 3 * l)) =
      G a ^ e * G (a ^ 3) ^ l * reciprocitySign a a ^ (e * l + l.choose 2) := by
  have hc : e = 0 ∨ e = 1 := by omega
  rcases hc with rfl | rfl
  · simpa only [zero_add, zero_mul, pow_zero, one_mul] using G_cube_power a ha l
  · rw [pow_add, pow_one, G_mul a (a ^ (3 * l)) ha (odd_residue_pow a ha _),
      G_cube_power a ha l, pow_mul, reciprocitySign_pow_right a (a ^ 3) ha l,
      reciprocitySign_cube_right a a ha ha]
    simp only [pow_one, one_mul, pow_add]
    ring

end SevenEighths.ProbePhase
end

end OAI

end Source495

/- Original source: OAI/NumberTheory/DirichletL/Detector/ReciprocityCRT.lean; sha256: 1c4a531823120481ddc6a92d8310fab6b9942461f31e48831480278ebb2e8d56 -/
section Source496
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein ProbePhase
local notation "O" => ActualEisensteinCubic.O

def reciprocityCoefficient (A s : O) (hA : A≠0) (H : O) : ℂ :=
  reciprocitySign A s * bareCongruenceCoefficient A s hA H

theorem reciprocityCoefficient_product (A B s r : O)
    (hA : Supported (Ideal.span {A})) (hB : Supported (Ideal.span {B}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpA : goodLambda^2∣A-1) (hpB : goodLambda^2∣B-1)
    (hps : goodLambda^2∣s-1) (hpr : goodLambda^2∣r-1)
    (hcop : IsCoprime (A*s) (B*r)) (H : O) :
    reciprocityCoefficient (A*B) (s*r)
      (mul_ne_zero (supportedElement_ne_zero A hA) (supportedElement_ne_zero B hB)) H =
      (idealRowHom B (Ideal.span {A}) * idealRowHom A (Ideal.span {B})) *
        reciprocityCoefficient A s (supportedElement_ne_zero A hA) H *
        reciprocityCoefficient B r (supportedElement_ne_zero B hB) H := by
  have hsB := idealRowHom_ne_zero_of_coprime s B hs hcop.of_mul_left_right.of_mul_right_left
  have hrA := idealRowHom_ne_zero_of_coprime r A hr hcop.of_mul_left_left.of_mul_right_right.symm
  have hAr : idealRowHom r (Ideal.span {A}) = reciprocitySign A r * idealRowHom A (Ideal.span {r}) :=
    idealRowHom_primary_reciprocity A r hpA hpr hA hr
  have hBs : idealRowHom s (Ideal.span {B}) = reciprocitySign B s * idealRowHom B (Ideal.span {s}) :=
    idealRowHom_primary_reciprocity B s hpB hps hB hs
  have hratio :
      (idealRowHom B (Ideal.span {A}) * idealRowHom r (Ideal.span {A}) *
       idealRowHom A (Ideal.span {B}) * idealRowHom s (Ideal.span {B})) /
      (idealRowHom B (Ideal.span {s}) * idealRowHom A (Ideal.span {r})) =
      (idealRowHom B (Ideal.span {A}) * idealRowHom A (Ideal.span {B})) *
        reciprocitySign A r * reciprocitySign B s := by
    rw [hAr, hBs]
    field_simp
  have hsign : reciprocitySign (A*B) (s*r) * reciprocitySign A r * reciprocitySign B s =
      reciprocitySign A s * reciprocitySign B r := by
    calc
      _ = reciprocitySign A s * reciprocitySign B r *
          reciprocitySign A r ^ 2 * reciprocitySign B s ^ 2 := by
        simp only [reciprocitySign_mul_left, reciprocitySign_mul_right]
        ring
      _ = _ := by
        rw [reciprocitySign_sq A r (supported_residue_odd A hA) (supported_residue_odd r hr),
          reciprocitySign_sq B s (supported_residue_odd B hB) (supported_residue_odd s hs),
          mul_one, mul_one]
  unfold reciprocityCoefficient
  rw [bareCongruenceCoefficient_product_reduced A B s r (supportedElement_ne_zero A hA)
    (supportedElement_ne_zero B hB) hs hr hcop H, hratio]
  calc
    _ = (reciprocitySign (A*B) (s*r) * reciprocitySign A r * reciprocitySign B s) *
        (idealRowHom B (Ideal.span {A}) * idealRowHom A (Ideal.span {B})) *
        bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H *
        bareCongruenceCoefficient B r (supportedElement_ne_zero B hB) H := by ring
    _ = _ := by rw [hsign]; ring

end SevenEighths.ProbePhysical
end

end OAI

end Source496

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/Algebra.lean; sha256: 1bbf98bbbd1c4ebc573dd6c53013e518d0d0c97897116bcd4eb96affdde07d38 -/
section Source497
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section

theorem square_eq_star_of_fourth_eq (z : ℂ) (hz : z ^ 4 = z) : z ^ 2 = star z := by
  by_cases h0 : z = 0
  · simp [h0]
  have h3 : z ^ 3 = 1 := by
    apply mul_right_cancel₀ h0
    simpa only [← pow_succ, one_mul] using hz
  have hn := Complex.norm_eq_one_of_pow_eq_one h3 (by decide : (3 : ℕ) ≠ 0)
  change z ^ 2 = (starRingEnd ℂ) z
  rw [← Complex.inv_eq_conj hn]
  apply mul_right_cancel₀ h0
  rw [inv_mul_cancel₀ h0]
  simpa only [← pow_succ] using h3

variable {R : Type*} [CommRing R] [Finite Rˣ]

omit [Finite Rˣ] in
theorem cubic_inv_eq_square (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) :
    χ⁻¹ = χ ^ 2 := by
  calc
    χ⁻¹ = χ⁻¹ * χ ^ 3 := by rw [hχ, mul_one]
    _ = χ ^ 2 := by group

theorem cubic_square_eq_star (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    χ x ^ 2 = star (χ x) := by
  rw [MulChar.star_apply', cubic_inv_eq_square χ hχ, MulChar.pow_apply' _ (by decide)]

omit [Finite Rˣ] in
theorem cubic_fourth_eq (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    χ x ^ 4 = χ x := by
  have h : χ ^ 4 = χ := by
    rw [show (4 : ℕ) = 3 + 1 by decide, pow_add, hχ, one_mul, pow_one]
  rw [← MulChar.pow_apply' χ (by decide : (4 : ℕ) ≠ 0), h]

omit [Finite Rˣ] in
theorem cubic_cube_eq_mask (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    χ (x ^ 3) = if IsUnit x then 1 else 0 := by
  classical
  rw [map_pow, ← MulChar.pow_apply' χ (by decide : (3 : ℕ) ≠ 0), hχ]
  by_cases hx : IsUnit x
  · rw [ite_eq_left hx, MulChar.one_apply hx]
  · rw [ite_eq_right hx, MulChar.map_nonunit _ hx]

theorem cubic_row_decomposition (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1)
    (a b c : R) :
    χ (a * b ^ 2 * c ^ 3) =
      χ a * star (χ b) * (if IsUnit c then 1 else 0) := by
  rw [map_mul, map_mul, map_pow, cubic_square_eq_star χ hχ,
    cubic_cube_eq_mask χ hχ]

omit [Finite Rˣ] in
theorem cubic_norm_le_one (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    ‖χ x‖ ≤ 1 := by
  by_cases hx : IsUnit x
  · have hc : χ x ^ 3 = 1 := by
      rw [← MulChar.pow_apply' χ (by decide : (3 : ℕ) ≠ 0), hχ, MulChar.one_apply hx]
    exact (Complex.norm_eq_one_of_pow_eq_one hc (by decide)).le
  · rw [MulChar.map_nonunit _ hx, norm_zero]
    exact zero_le_one

theorem row_decomposition_sum {ι M : Type*} [CommMonoid M]
    (S : Finset ι) (coef : ι → ℂ) (ρ : ι → M →* R)
    (χ : ι → MulChar R ℂ) (hχ : ∀ n ∈ S, χ n ^ 3 = 1)
    (a b c : M) :
    (∑ n ∈ S, coef n * χ n (ρ n (a * b ^ 2 * c ^ 3))) =
      ∑ n ∈ S,
        (coef n * star (χ n (ρ n b)) *
          (if IsUnit (ρ n c) then 1 else 0)) * χ n (ρ n a) := by
  classical
  apply Finset.sum_congr rfl
  intro n hn
  have hmap : ρ n (a * b ^ 2 * c ^ 3) =
      ρ n a * (ρ n b) ^ 2 * (ρ n c) ^ 3 := by simp only [map_mul, map_pow]
  rw [hmap, cubic_row_decomposition (χ n) (hχ n hn)]
  ring

omit [Finite Rˣ] in
theorem extracted_coefficients_energy_le {ι : Type*}
    (S : Finset ι) (coef : ι → ℂ) (χ : ι → MulChar R ℂ)
    (hχ : ∀ n ∈ S, χ n ^ 3 = 1) (b c : ι → R) :
    (∑ n ∈ S, ‖coef n * star (χ n (b n)) *
      (if IsUnit (c n) then (1 : ℂ) else 0)‖ ^ 2) ≤
      ∑ n ∈ S, ‖coef n‖ ^ 2 := by
  classical
  apply Finset.sum_le_sum
  intro n hn
  by_cases hc : IsUnit (c n)
  · simp only [ite_eq_left hc, mul_one, norm_mul, norm_star]
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_of_le_one_right (norm_nonneg _) (cubic_norm_le_one (χ n) (hχ n hn) _)
  · simp only [ite_eq_right hc, mul_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _

end
end SevenEighths.CubicSieve

end OAI

end Source497

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/Factorization.lean; sha256: fbdf1b9b8d00a6babd8cc925a9c65b069ae80c4471135981b8b1147e4ccb6a16 -/
section Source498
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open UniqueFactorizationMonoid
noncomputable section

variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]
  [NormalizationMonoid M] [Subsingleton Mˣ]

def firstPart (x : M) : M :=
  ∏ p ∈ (normalizedFactors x).toFinset.filter
    (fun p => (normalizedFactors x).count p % 3 = 1), p

def secondPart (x : M) : M :=
  ∏ p ∈ (normalizedFactors x).toFinset.filter
    (fun p => (normalizedFactors x).count p % 3 = 2), p

def cubePart (x : M) : M :=
  ∏ p ∈ (normalizedFactors x).toFinset, p ^ ((normalizedFactors x).count p / 3)

theorem count_mod_three (k : ℕ) :
    k = (if k % 3 = 1 then 1 else 0) +
      2 * (if k % 3 = 2 then 1 else 0) + 3 * (k / 3) := by
  have h := Nat.mod_add_div k 3
  have hlt := Nat.mod_lt k (by decide : 0 < 3)
  split_ifs <;> omega

omit [Subsingleton Mˣ] in
private theorem residual_squarefree (x : M) (r : ℕ) :
    Squarefree (∏ p ∈ (normalizedFactors x).toFinset.filter
      (fun p => (normalizedFactors x).count p % 3 = r), p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    have hp' : p ∈ normalizedFactors x := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hp).1
    have hq' : q ∈ normalizedFactors x := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hq).1
    apply (irreducible_of_normalized_factor p hp').isRelPrime_iff_not_dvd.mpr
    intro hd
    exact hpq (normalizedFactors_eq_of_dvd x p hp' q hq' hd)
  · intro p hp
    exact (irreducible_of_normalized_factor p
      (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hp).1)).squarefree

omit [Subsingleton Mˣ] in
theorem firstPart_squarefree (x : M) : Squarefree (firstPart x) :=
  residual_squarefree x 1

omit [Subsingleton Mˣ] in
theorem secondPart_squarefree (x : M) : Squarefree (secondPart x) :=
  residual_squarefree x 2

omit [Subsingleton Mˣ] in
theorem residual_parts_isRelPrime (x : M) : IsRelPrime (firstPart x) (secondPart x) := by
  unfold firstPart secondPart
  apply IsRelPrime.prod_left
  intro p hp
  apply IsRelPrime.prod_right
  intro q hq
  have hp' := Finset.mem_filter.mp hp
  have hq' := Finset.mem_filter.mp hq
  apply (irreducible_of_normalized_factor p (Multiset.mem_toFinset.mp hp'.1)).isRelPrime_iff_not_dvd.mpr
  intro hd
  have heq := normalizedFactors_eq_of_dvd x p (Multiset.mem_toFinset.mp hp'.1)
    q (Multiset.mem_toFinset.mp hq'.1) hd
  subst q
  omega

theorem cubic_factorization (x : M) (hx : x ≠ 0) :
    x = firstPart x * secondPart x ^ 2 * cubePart x ^ 3 := by
  have hp : (∏ p ∈ (normalizedFactors x).toFinset,
      p ^ (normalizedFactors x).count p) = x := by
    rw [← Finset.prod_multiset_count]
    exact associated_iff_eq.mp (prod_normalizedFactors hx)
  have hper (p : M) : p ^ (normalizedFactors x).count p =
      (if (normalizedFactors x).count p % 3 = 1 then p else 1) *
      (if (normalizedFactors x).count p % 3 = 2 then p else 1) ^ 2 *
      (p ^ ((normalizedFactors x).count p / 3)) ^ 3 := by
    conv_lhs => rw [count_mod_three ((normalizedFactors x).count p)]
    rw [pow_add, pow_add, Nat.mul_comm 3, pow_mul]
    split_ifs <;> simp [pow_mul]
  calc
    x = ∏ p ∈ (normalizedFactors x).toFinset,
        p ^ (normalizedFactors x).count p := hp.symm
    _ = firstPart x * secondPart x ^ 2 * cubePart x ^ 3 := by
      simp_rw [hper]
      simp only [Finset.prod_mul_distrib, Finset.prod_pow]
      simp only [firstPart, secondPart, cubePart, Finset.prod_filter]

theorem extraction_injective_on_nonzero :
    Set.InjOn (fun x : M => (firstPart x, secondPart x, cubePart x)) {x | x ≠ 0} := by
  intro x hx y hy h
  have h1 := congrArg (fun t : M × M × M => t.1) h
  have h2 := congrArg (fun t : M × M × M => t.2.1) h
  have h3 := congrArg (fun t : M × M × M => t.2.2) h
  dsimp only at h1 h2 h3
  rw [cubic_factorization x hx, cubic_factorization y hy, h1, h2, h3]

end
end SevenEighths.CubicSieve

end OAI

end Source498

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/Operator.lean; sha256: 45c1fea54b94c93894139673096df9080057485c2e6a1ea319a7d76e16d49612 -/
section Source499
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def operator (A : Matrix m n ℂ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m :=
  A.toEuclideanLin.toContinuousLinearMap

omit [DecidableEq m] in
@[simp] theorem operator_apply (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) (i : m) :
    operator A x i = ∑ j, A i j * x j := rfl

def squaredNorm (A : Matrix m n ℂ) : ℝ := ‖operator A‖ ^ 2

def conjugateVector (x : EuclideanSpace ℂ n) : EuclideanSpace ℂ n :=
  WithLp.toLp 2 (fun j => star (x j))

omit [Fintype n] [DecidableEq n] in
@[simp] theorem conjugateVector_apply (x : EuclideanSpace ℂ n) (j : n) :
    conjugateVector x j = star (x j) := rfl

omit [DecidableEq n] in
@[simp] theorem norm_conjugateVector (x : EuclideanSpace ℂ n) :
    ‖conjugateVector x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, conjugateVector_apply, norm_star]

omit [DecidableEq m] in
theorem operator_conjugate_apply (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    operator (fun i j => star (A i j)) x = conjugateVector (operator A (conjugateVector x)) := by
  ext i
  change (∑ j, star (A i j) * x j) = star (∑ j, A i j * star (x j))
  simp only [star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

omit [DecidableEq m] in
theorem operator_conjugate_norm_le (A : Matrix m n ℂ) :
    ‖operator (fun i j => star (A i j))‖ ≤ ‖operator A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [operator_conjugate_apply, norm_conjugateVector]
  simpa only [norm_conjugateVector] using (operator A).le_opNorm (conjugateVector x)

omit [DecidableEq m] in
theorem operator_conjugate_norm (A : Matrix m n ℂ) :
    ‖operator (fun i j => star (A i j))‖ = ‖operator A‖ := by
  apply le_antisymm (operator_conjugate_norm_le A)
  simpa only [star_star] using operator_conjugate_norm_le (fun i j => star (A i j))

theorem operator_conjTranspose_norm (A : Matrix m n ℂ) :
    ‖operator A.conjTranspose‖ = ‖operator A‖ := by
  have heq : operator A.conjTranspose = (operator A).adjoint := by
    unfold operator
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap]
  rw [heq]
  exact ContinuousLinearMap.adjoint.norm_map _

theorem squaredNorm_transpose (A : Matrix m n ℂ) :
    squaredNorm A.transpose = squaredNorm A := by
  unfold squaredNorm
  have h := operator_conjugate_norm A.transpose
  change ‖operator A.conjTranspose‖ = ‖operator A.transpose‖ at h
  rw [operator_conjTranspose_norm] at h
  exact congrArg (fun x : ℝ => x ^ 2) h.symm

theorem squaredNorm_reciprocity (A : Matrix m n ℂ) (B : Matrix n m ℂ)
    (hrecip : ∀ i j, A i j = B j i) : squaredNorm A = squaredNorm B := by
  have h : A = B.transpose := by ext i j; exact hrecip i j
  rw [h, squaredNorm_transpose]

omit [DecidableEq m] in
theorem energy_le_squaredNorm (A : Matrix m n ℂ) (c : n → ℂ) :
    (∑ i, ‖∑ j, A i j * c j‖ ^ 2) ≤ squaredNorm A * ∑ j, ‖c j‖ ^ 2 := by
  let x : EuclideanSpace ℂ n := WithLp.toLp 2 c
  have h := (operator A).le_opNorm x
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [squaredNorm, mul_pow, EuclideanSpace.norm_sq_eq, operator_apply, x] using hs

end
end SevenEighths.CubicSieve

end OAI

end Source499

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/Blocks.lean; sha256: 3b1eabe72ead4d84320af63d0a587e8f70a8107b92a4f47639649f7418d8c89d -/
section Source500
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section

variable {a b n : Type*} [Fintype a] [Fintype b] [Fintype n]
  [DecidableEq n]

theorem squaredNorm_nonneg (A : Matrix a n ℂ) : 0 ≤ squaredNorm A := sq_nonneg _

theorem masked_energy_le (A : Matrix a n ℂ) (coef phase : n → ℂ)
    (hphase : ∀ j, ‖phase j‖ ≤ 1) :
    (∑ i, ‖∑ j, A i j * (coef j * phase j)‖ ^ 2) ≤
      squaredNorm A * ∑ j, ‖coef j‖ ^ 2 := by
  apply (energy_le_squaredNorm A (fun j => coef j * phase j)).trans
  apply mul_le_mul_of_nonneg_left _ (squaredNorm_nonneg A)
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul]
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_of_le_one_right (norm_nonneg _) (hphase j)

theorem rectangular_block_energy_le
    (A : Matrix a n ℂ) (B : Matrix b n ℂ) (coef mask : n → ℂ)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ k j, ‖B k j‖ ≤ 1)
    (hmask : ∀ j, ‖mask j‖ ≤ 1) :
    (∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask j‖ ^ 2) ≤
      min ((Fintype.card b : ℝ) * squaredNorm A)
        ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by
  have hleft :
      (∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask j‖ ^ 2) ≤
        ((Fintype.card b : ℝ) * squaredNorm A) * ∑ j, ‖coef j‖ ^ 2 := by
    calc
      _ ≤ ∑ k : b, squaredNorm A * ∑ j, ‖coef j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        have h := masked_energy_le A coef (fun j => star (B k j) * mask j) (by
          intro j
          rw [norm_mul, norm_star]
          exact (mul_le_mul_of_nonneg_right (hB k j) (norm_nonneg _)).trans (by simpa using hmask j))
        simpa only [mul_assoc, mul_left_comm, mul_comm] using h
      _ = _ := by simp [mul_assoc]
  have hright :
      (∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask j‖ ^ 2) ≤
        ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ i : a, squaredNorm (fun k j => star (B k j)) * ∑ j, ‖coef j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have h := masked_energy_le (fun k j => star (B k j)) coef
          (fun j => A i j * mask j) (by
            intro j
            rw [norm_mul]
            exact (mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg _)).trans (by simpa using hmask j))
        simpa only [mul_assoc, mul_left_comm, mul_comm] using h
      _ = _ := by
        have hn : squaredNorm (fun k j => star (B k j)) = squaredNorm B := by
          unfold squaredNorm
          rw [operator_conjugate_norm]
        rw [hn]
        simp [mul_assoc]
  rcases le_total ((Fintype.card b : ℝ) * squaredNorm A)
      ((Fintype.card a : ℝ) * squaredNorm B) with h | h
  · rw [min_eq_left h]
    exact hleft
  · rw [min_eq_right h]
    exact hright

theorem cube_family_block_energy_le {c : Type*} [Fintype c]
    (A : Matrix a n ℂ) (B : Matrix b n ℂ) (coef : n → ℂ) (mask : c → n → ℂ)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ k j, ‖B k j‖ ≤ 1)
    (hmask : ∀ l j, ‖mask l j‖ ≤ 1) :
    (∑ l, ∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask l j‖ ^ 2) ≤
      (Fintype.card c : ℝ) *
        min ((Fintype.card b : ℝ) * squaredNorm A)
          ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by
  calc
    _ ≤ ∑ l : c, min ((Fintype.card b : ℝ) * squaredNorm A)
        ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro l _
      exact rectangular_block_energy_le A B coef (mask l) hA hB (hmask l)
    _ = _ := by simp [mul_assoc]

end
end SevenEighths.CubicSieve

end OAI

end Source500

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/Ideal.lean; sha256: f0ca6e538033b2b6b163e80dc70960b04a0c0f93ebc87565388e061a086c6086 -/
section Source501
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def Admissible (I : Ideal Eis) : Prop := Squarefree I ∧ primaryGenerator I ≠ 0

def idealKernel (I J : Ideal Eis) : ℂ :=
  eisEmbedding (CubicJacobiGlobal.idealSymbol I (primaryGenerator J))

theorem idealKernel_reciprocity (I J : Ideal Eis)
    (hI : primaryGenerator I ≠ 0) (hJ : primaryGenerator J ≠ 0) :
    idealKernel I J = idealKernel J I :=
  congrArg eisEmbedding (CubicJacobiGlobal.idealSymbol_reciprocity I J hI hJ)

theorem idealKernel_norm_le_one (I J : Ideal Eis) : ‖idealKernel I J‖ ≤ 1 := by
  rw [idealKernel, ← CanonicalRowCompletion.idealRowHom_square, norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (CanonicalRowCompletion.idealRowHom_norm (primaryGenerator J) I) 2).trans_eq (by norm_num)

theorem idealSymbol_fourth (I : Ideal Eis) (x : Eis) :
    (eisEmbedding (CubicJacobiGlobal.idealSymbol I x)) ^ 4 =
      eisEmbedding (CubicJacobiGlobal.idealSymbol I x) := by
  have hlocal (P : Ideal Eis) :
      (eisEmbedding (CubicJacobiGlobal.primeValue P x)) ^ 4 =
        eisEmbedding (CubicJacobiGlobal.primeValue P x) := by
    unfold CubicJacobiGlobal.primeValue
    split_ifs with h
    · let : P.IsMaximal := h.1
      let χ := actualSextic P h.2 ^ 2
      have hχ : χ ^ 3 = 1 := by
        dsimp [χ]
        rw [canonicalSextic_pow_two, MulChar.ringHomComp_pow, cubicChar_pow_three, MulChar.ringHomComp_one]
      simpa only [χ, canonicalSextic_pow_two, MulChar.ringHomComp_apply] using
        cubic_fourth_eq χ hχ (Ideal.Quotient.mk P x)
    · simp
  have hprod (S : Multiset (Ideal Eis)) :
      (eisEmbedding ((S.map (fun P => CubicJacobiGlobal.primeValue P x)).prod)) ^ 4 =
        eisEmbedding ((S.map (fun P => CubicJacobiGlobal.primeValue P x)).prod) := by
    induction S using Multiset.induction_on with
    | empty => simp
    | @cons P S ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, map_mul, mul_pow, hlocal, ih]
  by_cases hI : I = 0
  · simp [hI]
  · simpa only [CubicJacobiGlobal.idealSymbol, ite_eq_right hI] using
      hprod (UniqueFactorizationMonoid.normalizedFactors I)

theorem idealSymbol_cube_mask (I : Ideal Eis) (x : Eis)
    (hI : primaryGenerator I ≠ 0) :
    (eisEmbedding (CubicJacobiGlobal.idealSymbol I x)) ^ 3 =
      if IsCoprime I (Ideal.span {x}) then 1 else 0 := by
  have hlocal (P : Ideal Eis) (hP : P.IsMaximal ∧ goodLambda ∉ P) :
      (eisEmbedding (CubicJacobiGlobal.primeValue P x)) ^ 3 =
        if IsCoprime P (Ideal.span {x}) then 1 else 0 := by
    let : P.IsMaximal := hP.1
    let : Field (Eis ⧸ P) := Ideal.Quotient.field P
    let : Fintype (Eis ⧸ P) := Fintype.ofFinite _
    let χ := actualSextic P hP.2 ^ 2
    have hχ : χ ^ 3 = 1 :=
      (congrArg (fun φ : MulChar (Eis ⧸ P) ℂ => φ ^ 3)
        (canonicalSextic_pow_two P hP.2)).trans <|
          (MulChar.ringHomComp_pow _ _ _).trans <|
            (congrArg (fun φ : MulChar (Eis ⧸ P) Eis => φ.ringHomComp eisEmbedding)
              (cubicChar_pow_three P hP.2)).trans (MulChar.ringHomComp_one eisEmbedding)
    rw [CubicJacobiGlobal.primeValue_eq P hP.2]
    have hv := congrArg (fun φ : MulChar (Eis ⧸ P) ℂ => φ (Ideal.Quotient.mk P x))
      (canonicalSextic_pow_two P hP.2)
    change χ (Ideal.Quotient.mk P x) = _ at hv
    simp only [MulChar.ringHomComp_apply] at hv
    rw [← hv]
    rw [← map_pow, cubic_cube_eq_mask χ hχ, SixthPowerAverage.prime_coprime_span_iff]
    have hu : IsUnit (Ideal.Quotient.mk P x) ↔ x ∉ P := by
      rw [isUnit_iff_ne_zero, ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    simp only [hu]
    split_ifs <;> rfl
  have hprod (S : Multiset (Ideal Eis))
      (hS : ∀ P ∈ S, P.IsMaximal ∧ goodLambda ∉ P) :
      (eisEmbedding ((S.map (fun P => CubicJacobiGlobal.primeValue P x)).prod)) ^ 3 =
        if IsCoprime S.prod (Ideal.span {x}) then 1 else 0 := by
    induction S using Multiset.induction_on with
    | empty => simp only [Multiset.map_zero, Multiset.prod_zero, map_one, one_pow,
        isCoprime_one_left, ite_true]
    | @cons P S ih =>
      have hp := hS P (Multiset.mem_cons_self _ _)
      have ht := fun Q hQ => hS Q (Multiset.mem_cons_of_mem hQ)
      simp only [Multiset.map_cons, Multiset.prod_cons, map_mul, mul_pow,
        hlocal P hp, ih ht, IsCoprime.mul_left_iff]
      by_cases hP : IsCoprime P (Ideal.span {x}) <;>
        by_cases hS : IsCoprime S.prod (Ideal.span {x}) <;> simp [hP, hS]
  have hI0 := primaryGenerator_ne_zero_ideal I hI
  have hf : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
      P.IsMaximal ∧ goodLambda ∉ P := by
    intro P hP
    have h := primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI hP)
    exact ⟨h.1, h.2.1⟩
  have h := hprod (UniqueFactorizationMonoid.normalizedFactors I) hf
  rw [Ideal.prod_normalizedFactors_eq_self hI0] at h
  simpa only [CubicJacobiGlobal.idealSymbol, ite_eq_right hI0] using h

theorem idealKernel_square_eq_star (I J : Ideal Eis) :
    idealKernel I J ^ 2 = star (idealKernel I J) :=
  square_eq_star_of_fourth_eq _ (idealSymbol_fourth I (primaryGenerator J))

def idealNumeratorHom (I : Ideal Eis) (hI : primaryGenerator I ≠ 0) : Ideal Eis →* ℂ where
  toFun := idealKernel I
  map_one' := by
    change eisEmbedding (CubicJacobiGlobal.idealSymbol I (primaryGenerator 1)) = 1
    rw [primaryGenerator_one, CubicJacobiGlobal.idealSymbol_map_one I hI, map_one]
  map_mul' A B := by
    simp only [idealKernel, primaryGenerator_mul,
      CubicJacobiGlobal.idealSymbol_map_mul I hI, map_mul]

theorem idealKernel_row_decomposition (I A B C : Ideal Eis)
    (hI : primaryGenerator I ≠ 0) :
    idealKernel I (A * B ^ 2 * C ^ 3) =
      idealKernel I A * star (idealKernel I B) * idealKernel I C ^ 3 := by
  change idealNumeratorHom I hI (A * B ^ 2 * C ^ 3) = _
  rw [map_mul, map_mul, map_pow, map_pow]
  change idealKernel I A * idealKernel I B ^ 2 * idealKernel I C ^ 3 = _
  rw [idealKernel_square_eq_star]

def idealRange (X : ℝ) : Finset (Ideal Eis) :=
  (idealsUpTo ⌊X⌋₊).filter Admissible

theorem mem_idealRange {X : ℝ} {I : Ideal Eis} :
    I ∈ idealRange X ↔ Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ X := by
  rw [idealRange, Finset.mem_filter, mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hp, hN⟩, ha⟩
    refine ⟨ha, ?_⟩
    have hX : 0 ≤ X := by
      by_contra hn
      have hz : ⌊X⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hX)
  · rintro ⟨ha, hN⟩
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr ?_, Nat.le_floor hN⟩, ha⟩
    intro hz
    exact (primaryGenerator_ne_zero_ideal I ha.2) (Ideal.absNorm_eq_zero_iff.mp hz)

def idealMatrix (M N : ℝ) : Matrix (idealRange M) (idealRange N) ℂ :=
  fun I J => idealKernel J.val I.val

def sieveNorm (M N : ℝ) : ℝ := squaredNorm (idealMatrix M N)

theorem sieveNorm_reciprocity (M N : ℝ) : sieveNorm M N = sieveNorm N M := by
  apply squaredNorm_reciprocity
  intro I J
  exact idealKernel_reciprocity J.val I.val
    (mem_idealRange.mp J.property).1.2 (mem_idealRange.mp I.property).1.2

theorem ideal_energy_bound (M N : ℝ) (coef : idealRange N → ℂ) :
    (∑ I : idealRange M, ‖∑ J : idealRange N,
      idealKernel J.val I.val * coef J‖ ^ 2) ≤
        sieveNorm M N * ∑ J, ‖coef J‖ ^ 2 :=
  energy_le_squaredNorm (idealMatrix M N) coef

theorem family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (rows : m → Ideal Eis) (cols : n → Ideal Eis)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N : ℝ) (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    squaredNorm (fun i j => idealKernel (cols j) (rows i)) ≤ sieveNorm M N := by
  let r : m → idealRange M := fun i => ⟨rows i, mem_idealRange.mpr (hrows i)⟩
  let c : n → idealRange N := fun j => ⟨cols j, mem_idealRange.mpr (hcols j)⟩
  have hri : Function.Injective r := fun i j h => hr (congrArg Subtype.val h)
  have hci : Function.Injective c := fun i j h => hc (congrArg Subtype.val h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hri c hci (idealMatrix M N)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem ideal_cube_block_energy_le {a b c n : Type*}
    [Fintype a] [Fintype b] [Fintype c] [Fintype n]
    [DecidableEq a] [DecidableEq b] [DecidableEq n]
    (A : a → Ideal Eis) (B : b → Ideal Eis) (C : c → Ideal Eis)
    (cols : n → Ideal Eis) (hc : ∀ j, primaryGenerator (cols j) ≠ 0)
    (coef : n → ℂ) :
    (∑ l, ∑ k, ∑ i, ‖∑ j, coef j *
      idealKernel (cols j) (A i * B k ^ 2 * C l ^ 3)‖ ^ 2) ≤
      (Fintype.card c : ℝ) *
        min ((Fintype.card b : ℝ) * squaredNorm (fun i j => idealKernel (cols j) (A i)))
          ((Fintype.card a : ℝ) * squaredNorm (fun k j => idealKernel (cols j) (B k))) *
        ∑ j, ‖coef j‖ ^ 2 := by
  have he (i : a) (k : b) (l : c) :
      (∑ j, coef j * idealKernel (cols j) (A i * B k ^ 2 * C l ^ 3)) =
        ∑ j, idealKernel (cols j) (A i) * star (idealKernel (cols j) (B k)) *
          coef j * idealKernel (cols j) (C l) ^ 3 := by
    apply Finset.sum_congr rfl
    intro j _
    rw [idealKernel_row_decomposition _ _ _ _ (hc j)]
    ring
  simp_rw [he]
  apply cube_family_block_energy_le
  · exact fun i j => idealKernel_norm_le_one _ _
  · exact fun k j => idealKernel_norm_le_one _ _
  · intro l j
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) (idealKernel_norm_le_one _ _) 3).trans_eq (by norm_num)

theorem ideal_cubic_factorization (I : Ideal Eis) (hI : I ≠ 0) :
    I = firstPart I * secondPart I ^ 2 * cubePart I ^ 3 := cubic_factorization I hI

end
end SevenEighths.CubicSieve

end OAI

end Source501

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/Poisson.lean; sha256: f5af67bdbe06cc658e10c16dac2ac334d2e84b52304e2f09b881ab1df57d4cf4 -/
section Source502
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson QuadraticInitialBound
open CompletedGauss ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem canonical_finite_prime_gauss_transform_scalar_of_nontrivial
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, goodLambda ∉ P i)
    (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hgood i) ^ j i ≠ 1)
    (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) (h : O ⧸ ∏ i, P i) :
    (∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ (h * x)) =
      (finiteSexticQuotientRow P hc hgood j h)⁻¹ *
        ∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ x := by
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
  exact IdealGaussCRT.gauss_transform_finite_crt_scalar (fun i => O ⧸ P i)
    (IdealGaussCRT.quotientProdEquivPi P hc)
    (fun i => actualSextic (P i) (hgood i) ^ j i) ψ
    hχ h

theorem canonical_finite_prime_gauss_transform_conj_of_nontrivial
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, goodLambda ∉ P i)
    (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hgood i) ^ j i ≠ 1)
    (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) (h : O ⧸ ∏ i, P i) :
    (∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ (h * x)) =
      star (finiteSexticQuotientRow P hc hgood j h) *
        ∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ x := by
  rw [canonical_finite_prime_gauss_transform_scalar_of_nontrivial P hc hgood j hχ ψ,
    finiteSexticQuotientRow_inv_eq_star P hc hgood j h]

theorem canonical_principal_gauss_transform_of_nontrivial {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, goodLambda ∉ P i)
    (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hgood i) ^ j i ≠ 1)
    (c : O) (hc : Ideal.span {c} = ∏ i, P i)
    [Fintype (O ⧸ Ideal.span {c})]
    (ψ : AddChar (O ⧸ Ideal.span {c}) ℂ) (h : O ⧸ Ideal.span {c}) :
    (∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r * ψ (h * r)) =
      star (principalSexticRow P hcop hgood j c hc h) *
        ∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r * ψ r := by
  let e := Ideal.quotEquivOfEq hc
  let row := finiteSexticQuotientRow P hcop hgood j
  let φ : AddChar (O ⧸ ∏ i, P i) ℂ := ψ.compAddMonoidHom e.symm.toAddMonoidHom
  have hleft :
      (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ (h * r)) =
        ∑ x : O ⧸ ∏ i, P i, row x * φ (e h * x) := by
    rw [← Equiv.sum_comp e.toEquiv (fun x => row x * φ (e h * x))]
    apply Finset.sum_congr rfl
    intro r _
    change row (e r) * ψ (h * r) = row (e r) * ψ (e.symm (e h * e r))
    rw [← map_mul, e.symm_apply_apply]
  have hbase :
      (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ r) =
        ∑ x : O ⧸ ∏ i, P i, row x * φ x := by
    rw [← Equiv.sum_comp e.toEquiv (fun x => row x * φ x)]
    apply Finset.sum_congr rfl
    intro r _
    change row (e r) * ψ r = row (e r) * ψ (e.symm (e r))
    rw [e.symm_apply_apply]
  change (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ (h * r)) =
    star (row (e h)) * ∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ r
  rw [hleft, hbase]
  exact canonical_finite_prime_gauss_transform_conj_of_nontrivial P hcop hgood j hχ φ (e h)

theorem canonical_radial_poisson_of_nontrivial {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, goodLambda ∉ P i)
    (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hgood i) ^ j i ≠ 1)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus P
    let hc0 := finitePrimeModulus_ne_zero P
    let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
    let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let row := principalSexticRow P hcop hgood j c (span_finitePrimeModulus P)
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc0
    (∑' z : O, finiteSexticRow P hgood j z * W (‖eisEmbedding z‖ ^ 2 / scale)) =
      (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (star (finiteSexticRow P hgood j h) * (∑ r, row r * ψ r)) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  classical
  let c := finitePrimeModulus P
  have hc0 : c ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (span_finitePrimeModulus P)
  let : Fintype (O ⧸ ∏ i, P i) := Fintype.ofEquiv (O ⧸ Ideal.span {c}) e.toEquiv
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let row := principalSexticRow P hcop hgood j c (span_finitePrimeModulus P)
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc0
  have ht (h : O) :
      (∑ r : O ⧸ Ideal.span {c}, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) =
        star (finiteSexticRow P hgood j h) * (∑ r, row r * ψ r) := by
    rw [canonical_principal_gauss_transform_of_nontrivial P hcop hgood j hχ c
      (span_finitePrimeModulus P) ψ,
      principalSexticRow_mk P hcop hgood j c (span_finitePrimeModulus P) h]
  have hp := actual_radial_paper_poisson_trace W scale hscale c hc0 row
  change (∑' z : O, row (Ideal.Quotient.mk (Ideal.span {c}) z) *
    W (‖eisEmbedding z‖ ^ 2 / scale)) =
      (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, row r *
          ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) at hp
  simp_rw [ht] at hp
  simpa only [row, principalSexticRow_mk P hcop hgood j c
    (span_finitePrimeModulus P)] using hp

theorem canonical_radial_poisson_normalized_of_nontrivial {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, goodLambda ∉ P i)
    (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hgood i) ^ j i ≠ 1)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus P
    (∑' z : O, finiteSexticRow P hgood j z * W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * canonicalNormalizedGauss P hcop hgood j / (‖eisEmbedding c‖ : ℂ)) *
        ∑' h : O, star (finiteSexticRow P hgood j h) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  classical
  let c := finitePrimeModulus P
  let G := canonicalGaussSum P hcop hgood j
  let F : O → ℂ := fun h => star (finiteSexticRow P hgood j h) *
    paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)
  have hp := canonical_radial_poisson_of_nontrivial P hcop hgood j hχ W scale hscale
  change (∑' z : O, finiteSexticRow P hgood j z * W (‖eisEmbedding z‖ ^ 2 / scale)) =
    (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
      (star (finiteSexticRow P hgood j h) * G) *
        paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) at hp
  have hsum : (∑' h : O, (star (finiteSexticRow P hgood j h) * G) *
      paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)) =
      G * ∑' h : O, F h := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro h
    dsimp [F]
    ring
  rw [hsum] at hp
  rw [hp]
  change ((scale / ‖eisEmbedding c‖ ^ 2 : ℝ) : ℂ) * (G * ∑' h : O, F h) =
    ((scale : ℂ) * (G / (‖eisEmbedding c‖ : ℂ)) / (‖eisEmbedding c‖ : ℂ)) *
      ∑' h : O, F h
  have hn : (‖eisEmbedding c‖ : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr
      (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P)))
  push_cast
  field_simp

theorem norm_canonicalGaussSum_of_nontrivial {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, goodLambda ∉ P i)
    (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hgood i) ^ j i ≠ 1) :
    ‖canonicalGaussSum P hcop hgood j‖ = ‖eisEmbedding (finitePrimeModulus P)‖ := by
  classical
  let c := finitePrimeModulus P
  have hc0 : c ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
  let e : (O ⧸ Ideal.span {c}) ≃+* ∀ i, O ⧸ P i :=
    (Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
      (IdealGaussCRT.quotientProdEquivPi P hcop)
  let χ : ∀ i, MulChar (O ⧸ P i) ℂ := fun i => actualSextic (P i) (hgood i) ^ j i
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc0
  have hψ : ψ.IsPrimitive := GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc0
  have hnormsq := IdealGaussCRT.norm_gauss_finite_crt_sq (fun i => O ⧸ P i)
    e χ ψ hχ (fun i => IdealGaussCRT.coordinateAddChar_isPrimitive
      (fun i => O ⧸ P i) e ψ hψ i)
  change ‖canonicalGaussSum P hcop hgood j‖ ^ 2 =
    (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) at hnormsq
  have hcard : (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) = ‖eisEmbedding c‖ ^ 2 := by
    symm
    simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] using
      eisEmbedding_norm_sq_eq_absNorm_span c
  rw [hcard] at hnormsq
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnormsq

theorem norm_canonicalNormalizedGauss_of_nontrivial {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, goodLambda ∉ P i)
    (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hgood i) ^ j i ≠ 1) :
    ‖canonicalNormalizedGauss P hcop hgood j‖ = 1 := by
  have hn : ‖eisEmbedding (finitePrimeModulus P)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P))
  change ‖canonicalGaussSum P hcop hgood j /
    (‖eisEmbedding (finitePrimeModulus P)‖ : ℂ)‖ = 1
  rw [norm_div,
    norm_canonicalGaussSum_of_nontrivial P hcop hgood j hχ,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), div_self hn]

theorem canonical_polya_vinogradov_of_nontrivial {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hg i) ^ j i ≠ 1)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, finiteSexticRow P hg j z * W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      pvControl W * ‖eisEmbedding (finitePrimeModulus P)‖ := by
  let c := finitePrimeModulus P
  let q := ‖eisEmbedding c‖
  have hq : 0 < q := norm_pos_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P))
  let t := M / q ^ 2
  have ht : 0 < t := div_pos hM (sq_pos_of_pos hq)
  let F : O → ℂ := fun h => star (finiteSexticRow P hg j h) *
    paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)
  have hF (h : O) : ‖F h‖ ≤ ‖paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)‖ := by
    dsimp only [F]
    rw [norm_mul, norm_star]
    exact mul_le_of_le_one_left (norm_nonneg _) (finiteSexticRow_norm_le_one P hg j h)
  have hs := paperRadialFourier_lattice_summable_norm W t ht
  have hFs : Summable (fun h : O => ‖F h‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF hs
  have hzero : F 0 = 0 := by simp only [F, finiteSexticRow_zero P hg j, star_zero, zero_mul]
  have heq : (∑' h : O, F h) = ∑' h : {h : O // h ≠ 0}, F h := by
    symm
    apply tsum_subtype_eq_of_support_subset
    intro h hh hz
    subst h
    exact hh hzero
  have hn : ‖∑' h : O, F h‖ ≤
      ∑' h : {h : O // h ≠ 0}, ‖paperRadialFourier W (t * ‖eisEmbedding h.val‖ ^ 2)‖ := by
    rw [heq]
    exact (norm_tsum_le_tsum_norm (hFs.subtype _)).trans
      ((hFs.subtype _).tsum_le_tsum (fun h => hF h) (hs.subtype _))
  have hbound : t * ‖∑' h : O, F h‖ ≤ pvControl W :=
    (mul_le_mul_of_nonneg_left hn ht.le).trans (pv_lattice_bound W t ht)
  rw [canonical_radial_poisson_normalized_of_nontrivial P hcop hg j hχ W M hM]
  have hargs (h : O) : M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2 =
      t * ‖eisEmbedding h‖ ^ 2 := by dsimp [t, q]; ring
  change ‖((M : ℂ) * canonicalNormalizedGauss P hcop hg j / (q : ℂ)) *
    ∑' h : O, star (finiteSexticRow P hg j h) *
      paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)‖ ≤ _
  simp_rw [hargs]
  change ‖((M : ℂ) * canonicalNormalizedGauss P hcop hg j / (q : ℂ)) * ∑' h : O, F h‖ ≤ _
  rw [norm_mul, norm_div, norm_mul, norm_canonicalNormalizedGauss_of_nontrivial P hcop hg j hχ,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
  change M / q * ‖∑' h : O, F h‖ ≤ pvControl W * q
  calc
    _ = q * (t * ‖∑' h : O, F h‖) := by dsimp [t]; field_simp
    _ ≤ q * pvControl W := mul_le_mul_of_nonneg_left hbound hq.le
    _ = _ := mul_comm _ _

theorem canonical_masked_polya_vinogradov_of_nontrivial
    {α ι : Type*} [DecidableEq α] [Fintype ι] [Nonempty ι]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset α) (Q : ι → Ideal O) [∀ i, (Q i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime Q))
    (hg : ∀ i, goodLambda ∉ Q i) (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (Q i) (hg i) ^ j i ≠ 1)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, rowCoprimeMask P S z * finiteSexticRow Q hg j z *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      (2 : ℝ) ^ S.card * (pvControl W * ‖eisEmbedding (finitePrimeModulus Q)‖) := by
  rw [canonical_masked_radial_dilations P hinj S Q hcop hg j W M hM]
  calc
    _ ≤ ∑ E ∈ S.powerset, ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
        finiteSexticRow Q hg j (primeSubsetGenerator P E) *
        ∑' z : O, finiteSexticRow Q hg j z *
          W (‖eisEmbedding z‖ ^ 2 / (M / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _E ∈ S.powerset, pvControl W * ‖eisEmbedding (finitePrimeModulus Q)‖ := by
      apply Finset.sum_le_sum
      intro E hE
      rw [norm_mul, norm_mul]
      have hp := canonical_polya_vinogradov_of_nontrivial Q hcop hg j hχ W _
        (primeSubset_reducedScale_pos P E hM)
      have hmul : ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ)‖ *
          ‖finiteSexticRow Q hg j (primeSubsetGenerator P E)‖ ≤ 1 := by
        calc
          _ ≤ 1 * 1 := mul_le_mul (norm_ideal_moebius_le_one _)
            (finiteSexticRow_norm_le_one Q hg j _) (norm_nonneg _) zero_le_one
          _ = 1 := one_mul _
      exact (mul_le_of_le_one_left (norm_nonneg _) hmul).trans hp
    _ = _ := by simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

def cubicExponent (negative : Bool) : ℕ := if negative then 4 else 2

theorem cubicExponent_nonprincipal (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (negative : Bool) :
    actualSextic P hg ^ cubicExponent negative ≠ 1 := by
  let χ := actualSextic P hg ^ 2
  have hχ : χ ≠ 1 := by
    dsimp [χ]
    rw [canonicalSextic_pow_two P hg]
    exact (MulChar.ringHomComp_ne_one_iff eisEmbedding_injective).mpr (cubicChar_ne_one P hg)
  have h3 : χ ^ 3 = 1 := by
    dsimp [χ]
    rw [canonicalSextic_pow_two P hg, MulChar.ringHomComp_pow, cubicChar_pow_three P hg, MulChar.ringHomComp_one]
  have h2 : χ ^ 2 ≠ 1 := by
    intro h
    apply hχ
    calc
      χ = χ ^ 2 * χ := by rw [h, one_mul]
      _ = χ ^ 3 := (pow_succ χ 2).symm
      _ = 1 := h3
  cases negative with
  | false => simpa only [cubicExponent, Bool.false_eq_true, ite_false,
      ] using hχ
  | true =>
      have he : actualSextic P hg ^ 4 = χ ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul]
      simpa only [cubicExponent, ite_true, he] using h2

theorem cubic_radial_poisson {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (negative : ι → Bool)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' z : O, finiteSexticRow P hg (fun i => cubicExponent (negative i)) z *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * canonicalNormalizedGauss P hcop hg
        (fun i => cubicExponent (negative i)) / (‖eisEmbedding (finitePrimeModulus P)‖ : ℂ)) *
      ∑' h : O, star (finiteSexticRow P hg (fun i => cubicExponent (negative i)) h) *
        paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (finitePrimeModulus P)‖ ^ 2) :=
  canonical_radial_poisson_normalized_of_nontrivial P hcop hg _
    (fun i => cubicExponent_nonprincipal (P i) (hg i) (negative i)) W scale hscale

theorem cubic_polya_vinogradov {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (negative : ι → Bool)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    ‖∑' z : O, finiteSexticRow P hg (fun i => cubicExponent (negative i)) z *
      W (‖eisEmbedding z‖ ^ 2 / scale)‖ ≤
        pvControl W * ‖eisEmbedding (finitePrimeModulus P)‖ :=
  canonical_polya_vinogradov_of_nontrivial P hcop hg _
    (fun i => cubicExponent_nonprincipal (P i) (hg i) (negative i)) W scale hscale

end
end SevenEighths.CubicSieve

end OAI

end Source502

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/Initial.lean; sha256: 94cb7b370d645596caf23ce7648aeaede6252086a8913a7bf160b4fa2dc486bf -/
section Source503
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CompletedGauss ConcretePrimeRowBridge ShortDraftHeckeBridge QuadraticInitialBound
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def cubicFiniteRow {α : Type*} (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (S : Finset α) (z : O) : ℂ :=
  (finiteSquarefreeRow P hg S z) ^ 2

theorem cubicFiniteRow_eq_canonical {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (S : Finset α) (z : O) :
    cubicFiniteRow P hg S z =
      finiteSexticRow (fun i : S => P i.val) (fun i => hg i.val) (fun _ => 2) z := by
  simp only [cubicFiniteRow, finiteSexticRow, finiteSquarefreeRow,
    MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), Finset.prod_pow]
  rw [Finset.prod_coe_sort (s := S) (f := fun i => actualSextic (P i) (hg i) (Ideal.Quotient.mk (P i) z))]

def activeCubicExponent {α : Type*} [DecidableEq α]
    (S T : Finset α) (i : activeSupport S T) : ℕ :=
  if i.val ∈ S \ T then 4 else 2

theorem activeCubicExponent_nonprincipal {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hg : ∀ i, goodLambda ∉ P i)
    (S T : Finset α) (i : activeSupport S T) :
    actualSextic (P i.val) (hg i.val) ^ activeCubicExponent S T i ≠ 1 := by
  have h := cubicExponent_nonprincipal (P i.val) (hg i.val)
    (decide (i.val ∈ S \ T))
  simpa only [cubicExponent, activeCubicExponent, decide_eq_true_eq] using h

theorem cubicFiniteRow_pair_kernel {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (S T : Finset α) (z : O) :
    star (cubicFiniteRow P hg S z) * cubicFiniteRow P hg T z =
      rowCoprimeMask P (S ∩ T) z *
        finiteSexticRow (activePrimes P S T) (fun i => hg i.val)
          (activeCubicExponent S T) z := by
  have h := congrArg (fun v : ℂ => v ^ 2) (finiteSquarefreeRow_pair_activeSupport P hg S T z)
  have hm : rowCoprimeMask P (S ∩ T) z ^ 2 = rowCoprimeMask P (S ∩ T) z := by
    unfold rowCoprimeMask
    split_ifs <;> simp
  have hrow : finiteSexticRow (activePrimes P S T) (fun i => hg i.val)
        (activeExponent S T) z ^ 2 =
      finiteSexticRow (activePrimes P S T) (fun i => hg i.val)
        (activeCubicExponent S T) z := by
    unfold finiteSexticRow
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    have h6 : actualSextic (P i.val) (hg i.val) ^ 6 = 1 :=
      (pow_mul _ 2 3).trans <|
        (congrArg (fun φ : MulChar (O ⧸ P i.val) ℂ => φ ^ 3)
          (canonicalSextic_pow_two (P i.val) (hg i.val))).trans <|
            (MulChar.ringHomComp_pow _ _ _).trans <|
              (congrArg (fun φ : MulChar (O ⧸ P i.val) O => φ.ringHomComp eisEmbedding)
                (cubicChar_pow_three (P i.val) (hg i.val))).trans
                  (MulChar.ringHomComp_one eisEmbedding)
    rw [← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0)]
    apply congrArg (fun χ : MulChar (O ⧸ P i.val) ℂ => χ (Ideal.Quotient.mk (P i.val) z))
    change (actualSextic (P i.val) (hg i.val) ^ activeExponent S T i) ^ 2 = _
    unfold activeExponent activeCubicExponent
    split_ifs
    · rw [← pow_mul, show (5 * 2 : ℕ) = 4 + 6 by decide, pow_add, h6, mul_one]
    · simp
  simpa only [mul_pow, ← star_pow, hm, hrow, cubicFiniteRow] using h

theorem cubic_gram_offdiagonal {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, goodLambda ∉ P i)
    (S T : Finset α) (hne : S ≠ T) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, (star (cubicFiniteRow P hg S z) * cubicFiniteRow P hg T z) *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      (2 : ℝ) ^ (S ∩ T).card *
        (pvControl W * ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖) := by
  let : Nonempty (activeSupport S T) := (activeSupport_nonempty_of_ne hne).to_subtype
  simp_rw [cubicFiniteRow_pair_kernel P hg S T]
  exact canonical_masked_polya_vinogradov_of_nontrivial P hinj (S ∩ T) (activePrimes P S T)
    (activePrimes_pairwise_isCoprime P hinj S T) (fun i => hg i.val)
    (activeCubicExponent S T) (activeCubicExponent_nonprincipal P hg S T) W M hM

theorem cubic_gram_offdiagonal_of_norm_le {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, goodLambda ∉ P i)
    (S T : Finset α) (hne : S ≠ T) (N : ℝ) (hN : 0 ≤ N)
    (hS : supportNorm P S ≤ N) (hT : supportNorm P T ≤ N)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, (star (cubicFiniteRow P hg S z) * cubicFiniteRow P hg T z) *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤ pvControl W * N := by
  apply (cubic_gram_offdiagonal P hinj hg S T hne W M hM).trans
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (divisor_conductor_bound P S T N hN hS hT)
    (pvControl_nonneg W)

theorem cubicFiniteRow_norm_le_one {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (S : Finset α) (z : O) :
    ‖cubicFiniteRow P hg S z‖ ≤ 1 := by
  rw [cubicFiniteRow_eq_canonical]
  exact finiteSexticRow_norm_le_one _ _ _ _

theorem cubic_pair_summable {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (S T : Finset α)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => (star (cubicFiniteRow P hg S z) * cubicFiniteRow P hg T z) *
      W (‖eisEmbedding z‖ ^ 2 / M)) := by
  have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hM)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hW
  intro z
  rw [norm_mul, norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_mul (cubicFiniteRow_norm_le_one P hg S z) (cubicFiniteRow_norm_le_one P hg T z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

theorem cubic_gram_diagonal {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (S : Finset α)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    ‖∑' z : O, (star (cubicFiniteRow P hg S z) * cubicFiniteRow P hg S z) *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤ diagonalControl W * M := by
  have hMp : 0 < M := by linarith
  have hs := (cubic_pair_summable P hg S S W M hMp).norm
  have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hMp)
  refine (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum ?_ hW).trans
    (radial_weight_lattice_bound W M hM))
  intro z
  rw [norm_mul, norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_mul (cubicFiniteRow_norm_le_one P hg S z) (cubicFiniteRow_norm_le_one P hg S z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

private theorem norm_sq_finite_sum {β : Type*} (C : Finset β) (a r : β → ℂ) :
    (↑(‖∑ n ∈ C, a n * r n‖ ^ 2) : ℂ) =
      ∑ n ∈ C, ∑ m ∈ C, (star (a n) * a m) * (star (r n) * r m) := by
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, map_mul, starRingEnd_apply]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem cubic_mean_summable {α β : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (C : Finset β) (support : β → Finset α) (a : β → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * cubicFiniteRow P hg (support n) z‖ ^ 2) : ℂ)) := by
  have hs := summable_sum (s := C) (fun n hn => summable_sum (s := C) (fun m hm =>
    (cubic_pair_summable P hg (support n) (support m) W M hM).mul_left (star (a n) * a m)))
  apply hs.congr
  intro z
  rw [norm_sq_finite_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem cubic_mean_expand {α β : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (C : Finset β) (support : β → Finset α) (a : β → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * cubicFiniteRow P hg (support n) z‖ ^ 2) : ℂ)) =
      ∑ n ∈ C, ∑ m ∈ C, (star (a n) * a m) *
        ∑' z : O, (star (cubicFiniteRow P hg (support n) z) * cubicFiniteRow P hg (support m) z) *
          W (‖eisEmbedding z‖ ^ 2 / M) := by
  let f : β → β → O → ℂ := fun n m z => (star (a n) * a m) *
    ((star (cubicFiniteRow P hg (support n) z) * cubicFiniteRow P hg (support m) z) *
      W (‖eisEmbedding z‖ ^ 2 / M))
  have hf (n m : β) : Summable (f n m) :=
    (cubic_pair_summable P hg (support n) (support m) W M hM).mul_left _
  have heq (z : O) : W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * cubicFiniteRow P hg (support n) z‖ ^ 2) : ℂ) =
        ∑ n ∈ C, ∑ m ∈ C, f n m z := by
    rw [norm_sq_finite_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    dsimp [f]
    ring
  rw [tsum_congr heq, Summable.tsum_finsetSum (fun n hn => summable_sum (fun m hm => hf n m))]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Summable.tsum_finsetSum (fun m hm => hf n m)]
  apply Finset.sum_congr rfl
  intro m hm
  exact tsum_mul_left

theorem cubic_initial_mean_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, goodLambda ∉ P i)
    (C : Finset β) (support : β → Finset α)
    (hsupp : Set.InjOn support (↑C : Set β))
    (N : ℝ) (hN : 0 ≤ N) (hNorm : ∀ n ∈ C, supportNorm P (support n) ≤ N)
    (a : β → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    ‖∑' z : O, W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * cubicFiniteRow P hg (support n) z‖ ^ 2) : ℂ)‖ ≤
        (diagonalControl W * M + pvControl W * N * C.card) * ∑ n ∈ C, ‖a n‖ ^ 2 := by
  have hMp : 0 < M := by linarith
  let D := diagonalControl W * M
  let B := pvControl W * N
  have hB : 0 ≤ B := mul_nonneg (pvControl_nonneg W) hN
  let K : β → β → ℂ := fun n m => ∑' z : O,
    (star (cubicFiniteRow P hg (support n) z) * cubicFiniteRow P hg (support m) z) *
      W (‖eisEmbedding z‖ ^ 2 / M)
  have hK (n : β) (hn : n ∈ C) (m : β) (hm : m ∈ C) :
      ‖K n m‖ ≤ (if n = m then D else 0) + B := by
    by_cases hnm : n = m
    · subst m
      simp only [ite_true]
      exact (cubic_gram_diagonal P hg (support n) W M hM).trans (le_add_of_nonneg_right hB)
    · simp only [hnm, ite_false, zero_add]
      exact cubic_gram_offdiagonal_of_norm_le P hinj hg _ _
        (fun h => hnm (hsupp hn hm h)) N hN (hNorm n hn) (hNorm m hm) W M hMp
  have heq (n : β) (hn : n ∈ C) :
      (∑ m ∈ C, ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B)) =
        D * ‖a n‖ ^ 2 + B * ‖a n‖ * ∑ m ∈ C, ‖a m‖ := by
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq, hn, ite_true]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hcalc : (∑ n ∈ C, ∑ m ∈ C,
      ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B)) =
      D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * (∑ n ∈ C, ‖a n‖) ^ 2 := by
    rw [Finset.sum_congr rfl heq]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [cubic_mean_expand P hg C support a W M hMp]
  calc
    _ ≤ ∑ n ∈ C, ∑ m ∈ C, ‖(star (a n) * a m) * K n m‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ n ∈ C, ∑ m ∈ C, ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B) := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      simp only [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (hK n hn m hm) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * (∑ n ∈ C, ‖a n‖) ^ 2 := hcalc
    _ ≤ D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * ((C.card : ℝ) * ∑ n ∈ C, ‖a n‖ ^ 2) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ hB
      simpa only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, mul_comm] using
        Finset.sum_mul_sq_le_sq_mul_sq C (fun n => ‖a n‖) (fun _ => (1 : ℝ))
    _ = _ := by dsimp [D, B]; ring

theorem cubic_initial_finite_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, goodLambda ∉ P i)
    (C : Finset β) (support : β → Finset α) (hsupp : Set.InjOn support (↑C : Set β))
    (N : ℝ) (hN : 0 ≤ N) (hNorm : ∀ n ∈ C, supportNorm P (support n) ≤ N)
    (a : β → ℂ) (M : ℝ) (hM : 1 ≤ M) (R : Finset O)
    (hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M) :
    (∑ z ∈ R, ‖∑ n ∈ C, a n * cubicFiniteRow P hg (support n) z‖ ^ 2) ≤
      (diagonalControl sieveCutoff * M + pvControl sieveCutoff * N * C.card) *
        ∑ n ∈ C, ‖a n‖ ^ 2 := by
  have hMp : 0 < M := by linarith
  let E : O → ℝ := fun z => ‖∑ n ∈ C, a n * cubicFiniteRow P hg (support n) z‖ ^ 2
  let F : O → ℝ := fun z => sieveBump (‖eisEmbedding z‖ ^ 2 / M) * E z
  let H : O → ℂ := fun z => sieveCutoff (‖eisEmbedding z‖ ^ 2 / M) * (E z : ℂ)
  have hF (z : O) : 0 ≤ F z := mul_nonneg sieveBump.nonneg (sq_nonneg _)
  have hH (z : O) : H z = (F z : ℂ) := by
    simp only [H, F, sieveCutoff_apply, Complex.ofReal_mul]
  have hHs : Summable H := cubic_mean_summable P hg C support a sieveCutoff M hMp
  have hFs : Summable F := hHs.norm.congr (fun z => by
    rw [hH, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hF z)])
  have hsum : ‖∑' z : O, H z‖ = ∑' z : O, F z := by
    rw [tsum_congr hH, ← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (tsum_nonneg hF)]
  calc
    _ = ∑ z ∈ R, F z := by
      apply Finset.sum_congr rfl
      intro z hz
      have ht0 : 0 ≤ ‖eisEmbedding z‖ ^ 2 / M := div_nonneg (sq_nonneg _) hMp.le
      have ht1 : ‖eisEmbedding z‖ ^ 2 / M ≤ 1 := (div_le_one hMp).mpr (hR z hz)
      simp only [F, sieveBump_eq_one ht0 ht1, one_mul, E]
    _ ≤ ∑' z : O, F z := hFs.sum_le_tsum R (fun z _ => hF z)
    _ = ‖∑' z : O, H z‖ := hsum.symm
    _ ≤ _ := cubic_initial_mean_bound P hinj hg C support hsupp N hN hNorm
      a sieveCutoff M hM

theorem ideal_initial_cubic_sieve
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hsq : ∀ I ∈ F, Squarefree I)
    (N : ℕ) (hN : 1 ≤ N) (hnorm : ∀ I ∈ F, Ideal.absNorm I ≤ N)
    (a : Ideal O → ℂ) (M : ℝ) (hM : 1 ≤ M) (R : Finset O)
    (hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M) :
    (∑ z ∈ R, ‖∑ I ∈ F, a I * (idealSexticRow F hFpos hFgood I z) ^ 2‖ ^ 2) ≤
      initialSieveConstant * (M + (N : ℝ) ^ 2) * ∑ I ∈ F, ‖a I‖ ^ 2 := by
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsupp : Set.InjOn (idealSupport F) (↑F : Set (Ideal O)) := by
    intro I hI J hJ h
    exact idealSupport_injective_on_squarefree F hI hJ (hsq I hI) (hsq J hJ) h
  have hNorm (I : Ideal O) (hI : I ∈ F) :
      supportNorm (fun i : primePool F => i.val) (idealSupport F I) ≤ (N : ℝ) := by
    unfold supportNorm
    rw [idealSupport_product_eq F hI (hsq I hI)]
    exact_mod_cast hnorm I hI
  have hb := cubic_initial_finite_bound (fun i : primePool F => i.val)
    Subtype.val_injective (primePool_good F hFgood) F (idealSupport F) hsupp
    (N : ℝ) (by positivity) hNorm a M hM R hR
  change (∑ z ∈ R, ‖∑ I ∈ F, a I * (idealSexticRow F hFpos hFgood I z) ^ 2‖ ^ 2) ≤
    (diagonalControl sieveCutoff * M + pvControl sieveCutoff * (N : ℝ) * F.card) *
      ∑ I ∈ F, ‖a I‖ ^ 2 at hb
  have hsub : F ⊆ idealsUpTo N := by
    intro I hI
    apply mem_idealsUpTo.mpr
    constructor
    · apply Nat.one_le_iff_ne_zero.mpr
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]
      exact hFpos I hI
    · exact hnorm I hI
  have hcardNat : F.card ≤ 64 * (N + 1) :=
    (Finset.card_le_card hsub).trans (CompactScaleBridge.idealsUpTo_card_le N)
  have hcard : (F.card : ℝ) ≤ 128 * (N : ℝ) := by
    have hh : (F.card : ℝ) ≤ 64 * ((N : ℝ) + 1) := by exact_mod_cast hcardNat
    linarith
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hdiag := diagonalControl_nonneg sieveCutoff
  have hpv := pvControl_nonneg sieveCutoff
  have hmul := mul_le_mul_of_nonneg_left hcard (mul_nonneg hpv (by positivity : (0 : ℝ) ≤ N))
  unfold initialSieveConstant
  nlinarith [mul_nonneg hdiag (sq_nonneg (N : ℝ)),
    mul_nonneg hpv (show 0 ≤ M by linarith)]

end
end SevenEighths.CubicSieve

end OAI

end Source503

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/Norm.lean; sha256: 44aad4716899c8d675c1f1ed8075049d92a9733847ee00e5551803a9fb6f69d9 -/
section Source504
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem primaryGenerator_inj_on_cubic_admissible {I J : Ideal O}
    (hI : Admissible I) (hJ : Admissible J)
    (heq : primaryGenerator I = primaryGenerator J) : I = J := by
  calc
    I = Ideal.span {primaryGenerator I} := (primaryGenerator_spec I hI.2).1.symm
    _ = Ideal.span {primaryGenerator J} := by rw [heq]
    _ = J := (primaryGenerator_spec J hJ.2).1

theorem idealSymbol_eq_idealSexticRow_sq
    (F : Finset (Ideal O)) (hFp : ∀ I ∈ F, I ≠ ⊥)
    (hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I : Ideal O) (hI : I ∈ F) (hsq : Squarefree I) (z : O) :
    eisEmbedding (CubicJacobiGlobal.idealSymbol I z) =
      (idealSexticRow F hFp hFg I z) ^ 2 := by
  rw [← CanonicalRowCompletion.idealRowHom_square]
  congr 1
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFp
  conv_lhs => rw [← idealSupport_product_eq F hI hsq, map_prod]
  unfold idealSexticRow finiteSquarefreeRow
  apply Finset.prod_congr rfl
  intro i hi
  exact CanonicalRowCompletion.idealRowHom_prime z i.val (primePool_good F hFg i)

theorem sieveNorm_initial (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    sieveNorm M N ≤ QuadraticInitialBound.initialSieveConstant * (M + (⌈N⌉₊ : ℝ) ^ 2) := by
  let F := idealRange N
  let R := (idealRange M).image primaryGenerator
  have hF : ∀ I ∈ F, Admissible I := fun I hI => (mem_idealRange.mp hI).1
  have hFp : ∀ I ∈ F, I ≠ ⊥ := fun I hI => primaryGenerator_ne_zero_ideal I (hF I hI).2
  have hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P :=
    fun I hI P hP => (primaryPrime_spec P
      (primaryPrime_factor_ne_zero I P (hF I hI).2 hP)).2.1
  have hnat : 1 ≤ ⌈N⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  have hnorm : ∀ I ∈ F, Ideal.absNorm I ≤ ⌈N⌉₊ := by
    intro I hI
    exact Nat.cast_le.mp ((mem_idealRange.mp hI).2.trans (Nat.le_ceil N))
  have hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M := by
    intro z hz
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hz
    rw [primaryGenerator_norm_sq I ((mem_idealRange.mp hI).1.2)]
    exact (mem_idealRange.mp hI).2
  have hgen : Set.InjOn primaryGenerator (idealRange M) := by
    intro I hI J hJ heq
    exact primaryGenerator_inj_on_cubic_admissible (mem_idealRange.mp hI).1 (mem_idealRange.mp hJ).1 heq
  apply FiniteSieveOperator.squared_norm_le_of_energy (idealMatrix M N)
  · have hc := (QuadraticInitialBound.initialSieveConstant_pos).le
    positivity
  intro a
  let aext (I : Ideal O) : ℂ := if h : I ∈ F then a ⟨I, h⟩ else 0
  have hinner (z : O) :
      (∑ I ∈ F, aext I * (idealSexticRow F hFp hFg I z) ^ 2) =
        ∑ J : F, eisEmbedding (CubicJacobiGlobal.idealSymbol J.val z) * a J := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro J _
    rw [idealSymbol_eq_idealSexticRow_sq F hFp hFg J.val J.property (hF J.val J.property).1 z]
    simp only [aext, dite_eq_left J.property]
    change a J * (idealSexticRow F hFp hFg J.val z) ^ 2 =
      (idealSexticRow F hFp hFg J.val z) ^ 2 * a J
    exact mul_comm _ _
  have he := ideal_initial_cubic_sieve F hFp hFg
    (fun I hI => (hF I hI).1) ⌈N⌉₊ hnat hnorm aext M hM R hR
  have heR : (∑ z ∈ R, ‖∑ I ∈ F, aext I * (idealSexticRow F hFp hFg I z) ^ 2‖ ^ 2) =
      ∑ I : idealRange M, ‖∑ J : F, eisEmbedding (CubicJacobiGlobal.idealSymbol J.val (primaryGenerator I.val)) * a J‖ ^ 2 := by
    dsimp only [R]
    rw [Finset.sum_image (fun I hI J hJ heq => hgen hI hJ heq)]
    simp_rw [hinner]
    exact (Finset.sum_coe_sort _ _).symm
  have hea : (∑ I ∈ F, ‖aext I‖ ^ 2) = ∑ J : F, ‖a J‖ ^ 2 := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro J _
    simp only [aext, dite_eq_left J.property]
    rfl
  rw [heR, hea] at he
  exact he

end
end SevenEighths.CubicSieve

end OAI

end Source504

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/Extraction.lean; sha256: b9ab9c792d666079addc51bda93f261b34fdf2c372ee8d5947c2f43e14844fba -/
section Source505
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem primary_extracted_parts (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    primaryGenerator (firstPart I) ≠ 0 ∧ primaryGenerator (secondPart I) ≠ 0 ∧
      primaryGenerator (cubePart I) ≠ 0 := by
  have he := congrArg primaryGeneratorHom
    (cubic_factorization I (primaryGenerator_ne_zero_ideal I hI))
  simp only [map_mul, map_pow] at he
  change primaryGenerator I = primaryGenerator (firstPart I) *
    primaryGenerator (secondPart I) ^ 2 * primaryGenerator (cubePart I) ^ 3 at he
  rw [he, mul_ne_zero_iff, mul_ne_zero_iff, pow_ne_zero_iff (by decide : (2 : ℕ) ≠ 0),
    pow_ne_zero_iff (by decide : (3 : ℕ) ≠ 0)] at hI
  exact ⟨hI.1.1, hI.1.2, hI.2⟩

theorem firstPart_admissible (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    Admissible (firstPart I) := ⟨firstPart_squarefree I, (primary_extracted_parts I hI).1⟩

theorem secondPart_admissible (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    Admissible (secondPart I) := ⟨secondPart_squarefree I, (primary_extracted_parts I hI).2.1⟩

theorem extracted_norm_product (I : Ideal O) (hI : I ≠ 0) :
    (Ideal.absNorm I : ℝ) = (Ideal.absNorm (firstPart I) : ℝ) *
      (Ideal.absNorm (secondPart I) : ℝ) ^ 2 * (Ideal.absNorm (cubePart I) : ℝ) ^ 3 := by
  conv_lhs => rw [cubic_factorization I hI]
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]

theorem sieveNorm_mono {M N M' N' : ℝ} (hM : M ≤ M') (hN : N ≤ N') :
    sieveNorm M N ≤ sieveNorm M' N' := by
  apply family_squared_norm_le (fun I : idealRange M => I.val)
    (fun J : idealRange N => J.val) Subtype.val_injective Subtype.val_injective M' N'
  · intro I
    exact ⟨(mem_idealRange.mp I.property).1, (mem_idealRange.mp I.property).2.trans hM⟩
  · intro J
    exact ⟨(mem_idealRange.mp J.property).1, (mem_idealRange.mp J.property).2.trans hN⟩

end
end SevenEighths.CubicSieve

end OAI

end Source505

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/Elements.lean; sha256: 84fd15141c08dcf0c41df42416e726f03509a1611fc0c463400141e59bafefad -/
section Source506
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def elementCharacter (I : Ideal O) (hI : primaryGenerator I ≠ 0) : O →* ℂ where
  toFun x := eisEmbedding (CubicJacobiGlobal.idealSymbol I x)
  map_one' := by rw [CubicJacobiGlobal.idealSymbol_map_one I hI, map_one]
  map_mul' x y := by rw [CubicJacobiGlobal.idealSymbol_map_mul I hI, map_mul]

theorem elementCharacter_norm_le_one (I : Ideal O) (hI : primaryGenerator I ≠ 0) (x : O) :
    ‖elementCharacter I hI x‖ ≤ 1 := by
  change ‖eisEmbedding (CubicJacobiGlobal.idealSymbol I x)‖ ≤ 1
  rw [← CanonicalRowCompletion.idealRowHom_square, norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (CanonicalRowCompletion.idealRowHom_norm x I) 2).trans_eq (by norm_num)

theorem element_block_energy_le {a b c n : Type*}
    [Fintype a] [Fintype b] [Fintype c] [Fintype n]
    [DecidableEq a] [DecidableEq b] [DecidableEq n]
    (A : a → Ideal O) (B : b → Ideal O) (D : c → O)
    (cols : n → Ideal O) (hc : ∀ j, primaryGenerator (cols j) ≠ 0) (coef : n → ℂ) :
    (∑ l, ∑ k, ∑ i, ‖∑ j, coef j * elementCharacter (cols j) (hc j)
      (primaryGenerator (A i) * primaryGenerator (B k) ^ 2 * D l)‖ ^ 2) ≤
      (Fintype.card c : ℝ) *
        min ((Fintype.card b : ℝ) * squaredNorm (fun i j => idealKernel (cols j) (A i)))
          ((Fintype.card a : ℝ) * squaredNorm (fun k j => idealKernel (cols j) (B k))) *
        ∑ j, ‖coef j‖ ^ 2 := by
  have he (i : a) (k : b) (l : c) :
      (∑ j, coef j * elementCharacter (cols j) (hc j)
        (primaryGenerator (A i) * primaryGenerator (B k) ^ 2 * D l)) =
      ∑ j, idealKernel (cols j) (A i) * star (idealKernel (cols j) (B k)) *
        coef j * elementCharacter (cols j) (hc j) (D l) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, map_mul, map_pow]
    change coef j * (idealKernel (cols j) (A i) * idealKernel (cols j) (B k) ^ 2 *
      elementCharacter (cols j) (hc j) (D l)) = _
    rw [idealKernel_square_eq_star]
    ring
  simp_rw [he]
  apply cube_family_block_energy_le
  · exact fun i j => idealKernel_norm_le_one _ _
  · exact fun k j => idealKernel_norm_le_one _ _
  · exact fun l j => elementCharacter_norm_le_one _ _ _

def goodPart (I : Ideal O) : Ideal O := CanonicalQuadraticSieve.goodSquarefreePart I

def badPart (I : Ideal O) : Ideal O :=
  ∏ P ∈ CanonicalQuadraticSieve.badPrimeSupport I, P

theorem goodPart_admissible (I : Ideal O) : Admissible (goodPart I) := by
  have h := CanonicalQuadraticSieve.goodSquarefreePart_admissible I
  exact ⟨h.2.1, CanonicalQuadraticSieve.primaryGenerator_admissible _ h⟩

theorem badPart_mul_goodPart (I : Ideal O) (hI : Squarefree I) :
    badPart I * goodPart I = I := CanonicalQuadraticSieve.squarefree_bad_good_product I hI

def extractedGenerator (I : Ideal O) : O :=
  primaryGenerator (goodPart (firstPart I)) *
    primaryGenerator (goodPart (secondPart I)) ^ 2 *
    idealGenerator (cubePart I) ^ 3 *
    (idealGenerator (badPart (firstPart I)) * idealGenerator (badPart (secondPart I)) ^ 2)

theorem span_extractedGenerator (I : Ideal O) (hI : I ≠ 0) :
    Ideal.span {extractedGenerator I} = I := by
  change CanonicalRowCompletion.principalIdealHom (extractedGenerator I) = I
  unfold extractedGenerator
  simp only [map_mul, map_pow]
  change Ideal.span {primaryGenerator (goodPart (firstPart I))} *
    Ideal.span {primaryGenerator (goodPart (secondPart I))} ^ 2 *
    Ideal.span {idealGenerator (cubePart I)} ^ 3 *
    (Ideal.span {idealGenerator (badPart (firstPart I))} *
      Ideal.span {idealGenerator (badPart (secondPart I))} ^ 2) = I
  rw [(primaryGenerator_spec _ (goodPart_admissible (firstPart I)).2).1,
    (primaryGenerator_spec _ (goodPart_admissible (secondPart I)).2).1,
    span_idealGenerator, span_idealGenerator, span_idealGenerator]
  calc
    _ = (badPart (firstPart I) * goodPart (firstPart I)) *
        (badPart (secondPart I) * goodPart (secondPart I)) ^ 2 * cubePart I ^ 3 := by
      rw [mul_pow]
      simp only [mul_assoc, mul_left_comm, mul_comm]
    _ = firstPart I * secondPart I ^ 2 * cubePart I ^ 3 := by
      rw [badPart_mul_goodPart _ (firstPart_squarefree I),
        badPart_mul_goodPart _ (secondPart_squarefree I)]
    _ = I := (cubic_factorization I hI).symm

theorem element_cubic_extraction (z : O) (hz : z ≠ 0) :
    ∃ u : Oˣ, z = u.val * extractedGenerator (Ideal.span {z}) := by
  have hI : (Ideal.span {z} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hz
  have ha : Associated (extractedGenerator (Ideal.span {z})) z :=
    Ideal.span_singleton_eq_span_singleton.mp (span_extractedGenerator _ hI)
  obtain ⟨u, hu⟩ := ha
  exact ⟨u, by simpa only [mul_comm] using hu.symm⟩

theorem badPart_sector (I : Ideal O) :
    ∃ E : CanonicalQuadraticSieve.fixedBadPrimes.powerset, badPart I = ∏ P ∈ E.val, P := by
  exact ⟨⟨CanonicalQuadraticSieve.badPrimeSupport I,
    Finset.mem_powerset.mpr (CanonicalQuadraticSieve.badPrimeSupport_subset I)⟩, rfl⟩

end
end SevenEighths.CubicSieve

end OAI

end Source506

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/FullExtraction.lean; sha256: 8dcc9e91401df27db94db3fa37cf9221bd4edb801883d9c10c7a66b129f1482c -/
section Source507
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def firstImage (R : Finset O) : Finset (Ideal O) :=
  R.image (fun z => goodPart (firstPart (Ideal.span {z})))
def secondImage (R : Finset O) : Finset (Ideal O) :=
  R.image (fun z => goodPart (secondPart (Ideal.span {z})))
def cubeImage (R : Finset O) : Finset (Ideal O) :=
  R.image (fun z => cubePart (Ideal.span {z}))

def sourceFactor (R : Finset O)
    (d : Oˣ × CanonicalQuadraticSieve.fixedBadPrimes.powerset ×
      CanonicalQuadraticSieve.fixedBadPrimes.powerset × cubeImage R) : O :=
  d.1.val * idealGenerator d.2.2.2.val ^ 3 *
    (idealGenerator (∏ P ∈ d.2.1.val, P) * idealGenerator (∏ P ∈ d.2.2.1.val, P) ^ 2)

theorem full_element_extraction_energy {n : Type*} [Fintype n] [DecidableEq n]
    (R : Finset O) (hR : ∀ z ∈ R, z ≠ 0)
    (cols : n → Ideal O) (hc : ∀ j, primaryGenerator (cols j) ≠ 0) (coef : n → ℂ) :
    (∑ z ∈ R, ‖∑ j, coef j * elementCharacter (cols j) (hc j) z‖ ^ 2) ≤
      (96 : ℝ) * (cubeImage R).card *
        min ((secondImage R).card * squaredNorm
            (fun (i : firstImage R) j => idealKernel (cols j) i.val))
          ((firstImage R).card * squaredNorm
            (fun (k : secondImage R) j => idealKernel (cols j) k.val)) *
        ∑ j, ‖coef j‖ ^ 2 := by
  let : Finite Oˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Oˣ := Fintype.ofFinite _
  let D := Oˣ × CanonicalQuadraticSieve.fixedBadPrimes.powerset ×
    CanonicalQuadraticSieve.fixedBadPrimes.powerset × cubeImage R
  let T := D × secondImage R × firstImage R
  let reconstruct : T → O := fun p => primaryGenerator p.2.2.val *
    primaryGenerator p.2.1.val ^ 2 * sourceFactor R p.1
  let E : O → ℝ := fun z => ‖∑ j, coef j * elementCharacter (cols j) (hc j) z‖ ^ 2
  have hcover : R ⊆ Finset.univ.image reconstruct := by
    intro z hz
    let I : Ideal O := Ideal.span {z}
    obtain ⟨u, hu⟩ := element_cubic_extraction z (hR z hz)
    obtain ⟨e, he⟩ := badPart_sector (firstPart I)
    obtain ⟨f, hf⟩ := badPart_sector (secondPart I)
    let a : firstImage R := ⟨goodPart (firstPart I), Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    let b : secondImage R := ⟨goodPart (secondPart I), Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    let c : cubeImage R := ⟨cubePart I, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    refine Finset.mem_image.mpr ⟨((u, e, f, c), b, a), Finset.mem_univ _, ?_⟩
    change primaryGenerator (goodPart (firstPart I)) *
      primaryGenerator (goodPart (secondPart I)) ^ 2 *
        (u.val * idealGenerator (cubePart I) ^ 3 *
          (idealGenerator (∏ P ∈ e.val, P) * idealGenerator (∏ P ∈ f.val, P) ^ 2)) = z
    rw [hu]
    change _ = u.val * extractedGenerator I
    unfold extractedGenerator
    rw [he, hf]
    ring
  have hsum : (∑ z ∈ R, E z) ≤ ∑ p : T, E (reconstruct p) := by
    calc
      _ ≤ ∑ z ∈ Finset.univ.image reconstruct, E z :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover (fun _ _ _ => sq_nonneg _)
      _ ≤ _ := Finset.sum_image_le_of_nonneg (fun _ _ => sq_nonneg _)
  have hb := element_block_energy_le
    (fun i : firstImage R => i.val) (fun k : secondImage R => k.val)
    (sourceFactor R) cols hc coef
  have hcard : Fintype.card D = 96 * (cubeImage R).card := by
    have hu : Fintype.card Oˣ = 6 := by
      simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six
    simp only [D, Fintype.card_prod, Fintype.card_coe, hu,
      CanonicalQuadraticSieve.fixedBadPrimes_powerset_card]
    omega
  have heq : (∑ p : T, E (reconstruct p)) =
      ∑ l : D, ∑ k : secondImage R, ∑ i : firstImage R,
        ‖∑ j, coef j * elementCharacter (cols j) (hc j)
          (primaryGenerator i.val * primaryGenerator k.val ^ 2 * sourceFactor R l)‖ ^ 2 := by
    simp only [T, Fintype.sum_prod_type, E, reconstruct]
  rw [heq] at hsum
  apply hsum.trans
  dsimp only [D] at hcard
  convert hb using 1
  simp only [hcard, Nat.cast_mul, Nat.cast_ofNat, Fintype.card_coe]

end
end SevenEighths.CubicSieve

end OAI

end Source507

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/ExtractionBounds.lean; sha256: d6da5537a3a859a5502f63753567375cc4caa55e01c0baea6274b6ae1c031cd4 -/
section Source508
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem extracted_parts_ne_zero (I : Ideal O) (hI : I ≠ 0) :
    firstPart I ≠ 0 ∧ secondPart I ≠ 0 ∧ cubePart I ≠ 0 := by
  have he := cubic_factorization I hI
  rw [he, mul_ne_zero_iff, mul_ne_zero_iff,
    pow_ne_zero_iff (by decide : (2 : ℕ) ≠ 0),
    pow_ne_zero_iff (by decide : (3 : ℕ) ≠ 0)] at hI
  exact ⟨hI.1.1, hI.1.2, hI.2⟩

theorem goodPart_norm_le (I : Ideal O) (hI : Squarefree I) :
    (Ideal.absNorm (goodPart I) : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast CanonicalQuadraticSieve.goodSquarefreePart_norm_le I hI

theorem full_element_extraction_norm_bound {n : Type*} [Fintype n] [DecidableEq n]
    (R : Finset O) (hR : ∀ z ∈ R, z ≠ 0)
    (X Y H N : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hH : 1 ≤ H)
    (hfirst : ∀ z ∈ R, (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ≤ X)
    (hsecond : ∀ z ∈ R, (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ≤ Y)
    (hcube : ∀ z ∈ R, (Ideal.absNorm (cubePart (Ideal.span {z})) : ℝ) ≤ H)
    (cols : n → Ideal O) (hinj : Function.Injective cols)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (coef : n → ℂ) :
    (∑ z ∈ R, ‖∑ j, coef j * elementCharacter (cols j) (hcols j).1.2 z‖ ^ 2) ≤
      (96 * 128 ^ 2 : ℝ) * H *
        min (Y * sieveNorm X N) (X * sieveNorm Y N) * ∑ j, ‖coef j‖ ^ 2 := by
  have ha : ∀ I ∈ firstImage R, Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ X := by
    intro I hI
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
    exact ⟨goodPart_admissible _, (goodPart_norm_le _ (firstPart_squarefree _)).trans (hfirst z hz)⟩
  have hb : ∀ I ∈ secondImage R, Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ Y := by
    intro I hI
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
    exact ⟨goodPart_admissible _, (goodPart_norm_le _ (secondPart_squarefree _)).trans (hsecond z hz)⟩
  have hca : ((firstImage R).card : ℝ) ≤ 128 * X :=
    DescentFiberCost.finite_ideal_count_real _ X hX
      (fun I hI => primaryGenerator_ne_zero_ideal I (ha I hI).1.2) (fun I hI => (ha I hI).2)
  have hcb : ((secondImage R).card : ℝ) ≤ 128 * Y :=
    DescentFiberCost.finite_ideal_count_real _ Y hY
      (fun I hI => primaryGenerator_ne_zero_ideal I (hb I hI).1.2) (fun I hI => (hb I hI).2)
  have hcc : ((cubeImage R).card : ℝ) ≤ 128 * H := by
    apply DescentFiberCost.finite_ideal_count_real _ H hH
    · intro I hI
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
      exact (extracted_parts_ne_zero _ (Ideal.span_singleton_eq_bot.not.mpr (hR z hz))).2.2
    · intro I hI
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
      exact hcube z hz
  have hna := family_squared_norm_le (fun I : firstImage R => I.val) cols
    Subtype.val_injective hinj X N (fun I => ha I.val I.property) hcols
  have hnb := family_squared_norm_le (fun I : secondImage R => I.val) cols
    Subtype.val_injective hinj Y N (fun I => hb I.val I.property) hcols
  have hmin : min ((secondImage R).card * squaredNorm
      (fun (i : firstImage R) j => idealKernel (cols j) i.val))
      ((firstImage R).card * squaredNorm
      (fun (k : secondImage R) j => idealKernel (cols j) k.val)) ≤
      128 * min (Y * sieveNorm X N) (X * sieveNorm Y N) := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 128)]
    apply min_le_min
    · calc
        _ ≤ (128 * Y) * sieveNorm X N := mul_le_mul hcb hna (squaredNorm_nonneg _) (by positivity)
        _ = _ := by ring
    · calc
        _ ≤ (128 * X) * sieveNorm Y N := mul_le_mul hca hnb (squaredNorm_nonneg _) (by positivity)
        _ = _ := by ring
  have hn : 0 ≤ min ((secondImage R).card * squaredNorm
      (fun (i : firstImage R) j => idealKernel (cols j) i.val))
      ((firstImage R).card * squaredNorm
      (fun (k : secondImage R) j => idealKernel (cols j) k.val)) := by
    exact le_min (mul_nonneg (Nat.cast_nonneg _) (squaredNorm_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) (squaredNorm_nonneg _))
  calc
    _ ≤ _ := full_element_extraction_energy R hR cols (fun j => (hcols j).1.2) coef
    _ ≤ (96 * (128 * H)) * (128 * min (Y * sieveNorm X N) (X * sieveNorm Y N)) *
        ∑ j, ‖coef j‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcc (by norm_num)) hmin hn (by positivity)
    _ = _ := by ring

theorem cubePart_norm_le_of_block (I : Ideal O) (hI : I ≠ 0)
    (X Y H : ℝ) (hX : 0 < X) (hY : 0 < Y) (hH : 0 ≤ H)
    (hx : X ≤ (Ideal.absNorm (firstPart I) : ℝ))
    (hy : Y ≤ (Ideal.absNorm (secondPart I) : ℝ))
    (hN : (Ideal.absNorm I : ℝ) ≤ X * Y ^ 2 * H ^ 3) :
    (Ideal.absNorm (cubePart I) : ℝ) ≤ H := by
  have hp := extracted_norm_product I hI
  have hxy : X * Y ^ 2 ≤ (Ideal.absNorm (firstPart I) : ℝ) *
      (Ideal.absNorm (secondPart I) : ℝ) ^ 2 :=
    mul_le_mul hx (pow_le_pow_left₀ hY.le hy 2) (sq_nonneg _) (Nat.cast_nonneg _)
  apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) hH
  apply (mul_le_mul_iff_right₀ (mul_pos hX (sq_pos_of_pos hY))).mp
  calc
    _ ≤ (Ideal.absNorm (firstPart I) : ℝ) *
        (Ideal.absNorm (secondPart I) : ℝ) ^ 2 *
        (Ideal.absNorm (cubePart I) : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right hxy (by positivity)
    _ = Ideal.absNorm I := hp.symm
    _ ≤ _ := hN

theorem full_element_dyadic_block_bound {n : Type*} [Fintype n] [DecidableEq n]
    (R : Finset O) (hR : ∀ z ∈ R, z ≠ 0)
    (M X Y N : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hXY : X * Y ^ 2 ≤ M)
    (hfirst : ∀ z ∈ R, X ≤ (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ∧
      (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ≤ 2 * X)
    (hsecond : ∀ z ∈ R, Y ≤ (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ∧
      (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ≤ 2 * Y)
    (hnorm : ∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (cols : n → Ideal O) (hinj : Function.Injective cols)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (coef : n → ℂ) :
    (∑ z ∈ R, ‖∑ j, coef j * elementCharacter (cols j) (hcols j).1.2 z‖ ^ 2) ≤
      (192 * 128 ^ 2 : ℝ) * (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) *
        min (Y * sieveNorm (2 * X) N) (X * sieveNorm (2 * Y) N) * ∑ j, ‖coef j‖ ^ 2 := by
  have hp : 0 < X * Y ^ 2 := by positivity
  have hq : 1 ≤ M / (X * Y ^ 2) := (le_div_iff₀ hp).mpr (by simpa using hXY)
  have hH : 1 ≤ (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) :=
    Real.one_le_rpow hq (by norm_num)
  have hpow : ((M / (X * Y ^ 2)) ^ (1 / 3 : ℝ)) ^ 3 = M / (X * Y ^ 2) := by
    simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (by linarith : 0 ≤ M / (X * Y ^ 2)) (by decide : (3 : ℕ) ≠ 0)
  have hcube : ∀ z ∈ R, (Ideal.absNorm (cubePart (Ideal.span {z})) : ℝ) ≤
      (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) := by
    intro z hz
    apply cubePart_norm_le_of_block _ (Ideal.span_singleton_eq_bot.not.mpr (hR z hz))
      X Y _ (by linarith) (by linarith) (by linarith) (hfirst z hz).1 (hsecond z hz).1
    rw [hpow, mul_div_cancel₀ _ hp.ne']
    exact hnorm z hz
  have hb := full_element_extraction_norm_bound R hR (2 * X) (2 * Y) _ N
    (by linarith) (by linarith) hH (fun z hz => (hfirst z hz).2)
    (fun z hz => (hsecond z hz).2) hcube cols hinj hcols coef
  convert hb using 1
  have hm : min (2 * Y * sieveNorm (2 * X) N) (2 * X * sieveNorm (2 * Y) N) =
      2 * min (Y * sieveNorm (2 * X) N) (X * sieveNorm (2 * Y) N) := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1 <;> ring
  rw [hm]
  ring

end
end SevenEighths.CubicSieve

end OAI

end Source508

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/Dyadic.lean; sha256: b715496a642627823a3d71ad86f043e83038ba92699a16060626d25d6cca295b -/
section Source509
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma extracted_norm_bounds (I : Ideal O) (hI : I ≠ 0) :
    (1 ≤ (Ideal.absNorm (firstPart I) : ℝ) ∧
      (Ideal.absNorm (firstPart I) : ℝ) ≤ Ideal.absNorm I) ∧
    (1 ≤ (Ideal.absNorm (secondPart I) : ℝ) ∧
      (Ideal.absNorm (secondPart I) : ℝ) ≤ Ideal.absNorm I) := by
  have hn : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hp := extracted_parts_ne_zero I hI
  have ha : 1 ≤ Ideal.absNorm (firstPart I) :=
    Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp.1)
  have hb : 1 ≤ Ideal.absNorm (secondPart I) :=
    Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp.2.1)
  have hda : firstPart I ∣ I := ⟨secondPart I ^ 2 * cubePart I ^ 3, by
    simpa only [mul_assoc] using cubic_factorization I hI⟩
  have hdb : secondPart I ∣ I := ⟨firstPart I * secondPart I * cubePart I ^ 3, by
    calc
      I = firstPart I * secondPart I ^ 2 * cubePart I ^ 3 := cubic_factorization I hI
      _ = _ := by ring⟩
  exact ⟨⟨by exact_mod_cast ha, by exact_mod_cast Nat.le_of_dvd hn (map_dvd Ideal.absNorm hda)⟩,
    ⟨by exact_mod_cast hb, by exact_mod_cast Nat.le_of_dvd hn (map_dvd Ideal.absNorm hdb)⟩⟩

def extractionLabel (M : ℝ) (z : O) :
    Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
      Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) :=
  (CanonicalQuadraticSieve.divisorDyadicLabel M (firstPart (Ideal.span {z})),
   CanonicalQuadraticSieve.divisorDyadicLabel M (secondPart (Ideal.span {z})))

def extractionBin (R : Finset O) (M : ℝ)
    (j : Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
      Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1)) : Finset O :=
  R.filter (fun z => extractionLabel M z = j)

lemma sum_extractionBins {A : Type*} [AddCommMonoid A] (R : Finset O) (M : ℝ) (f : O → A) :
    (∑ z ∈ R, f z) = ∑ j, ∑ z ∈ extractionBin R M j, f z := by
  simp only [extractionBin, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  simp

lemma extractionBin_bounds (R : Finset O) (M : ℝ)
    (hR : ∀ z ∈ R, z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (j : Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
      Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1))
    (z : O) (hz : z ∈ extractionBin R M j) :
    (CanonicalQuadraticSieve.divisorDyadicScale j.1.val ≤
        (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ∧
      (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ≤
        2 * CanonicalQuadraticSieve.divisorDyadicScale j.1.val) ∧
    (CanonicalQuadraticSieve.divisorDyadicScale j.2.val ≤
        (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ∧
      (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ≤
        2 * CanonicalQuadraticSieve.divisorDyadicScale j.2.val) := by
  obtain ⟨hzR, hj⟩ := Finset.mem_filter.mp hz
  have hparts := extracted_norm_bounds (Ideal.span {z})
    (Ideal.span_singleton_eq_bot.not.mpr (hR z hzR).1)
  have hx := CanonicalQuadraticSieve.divisorDyadicLabel_bounds M _ hparts.1.1
    (hparts.1.2.trans (hR z hzR).2)
  have hy := CanonicalQuadraticSieve.divisorDyadicLabel_bounds M _ hparts.2.1
    (hparts.2.2.trans (hR z hzR).2)
  have hj1 := congrArg Prod.fst hj
  have hj2 := congrArg Prod.snd hj
  change CanonicalQuadraticSieve.divisorDyadicLabel M _ = j.1 at hj1
  change CanonicalQuadraticSieve.divisorDyadicLabel M _ = j.2 at hj2
  rw [hj1] at hx
  rw [hj2] at hy
  refine ⟨⟨max_le hparts.1.1 hx.1.le, ?_⟩, ⟨max_le hparts.2.1 hy.1.le, ?_⟩⟩
  · have hm := le_max_right (1 : ℝ) ((2 : ℝ)^j.1.val/2)
    change _ ≤ 2 * max 1 _
    linarith [hx.2]
  · have hm := le_max_right (1 : ℝ) ((2 : ℝ)^j.2.val/2)
    change _ ≤ 2 * max 1 _
    linarith [hy.2]

lemma extractionBin_scale_product (R : Finset O) (M : ℝ)
    (hR : ∀ z ∈ R, z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (j : Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
      Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1))
    (hj : (extractionBin R M j).Nonempty) :
    CanonicalQuadraticSieve.divisorDyadicScale j.1.val *
      CanonicalQuadraticSieve.divisorDyadicScale j.2.val ^ 2 ≤ M := by
  obtain ⟨z, hz⟩ := hj
  have hzR := (Finset.mem_filter.mp hz).1
  have hI : (Ideal.span {z} : Ideal O) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (hR z hzR).1
  have hh := extractionBin_bounds R M hR j z hz
  have hcube : 1 ≤ (Ideal.absNorm (cubePart (Ideal.span {z})) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (extracted_parts_ne_zero _ hI).2.2)
  calc
    _ ≤ (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) *
        (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ^ 2 :=
      mul_le_mul hh.1.1 (pow_le_pow_left₀
        (le_trans (by norm_num) (CanonicalQuadraticSieve.divisorDyadicScale_ge_one _)) hh.2.1 2)
        (sq_nonneg _) (Nat.cast_nonneg _)
    _ ≤ (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) *
        (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ^ 2 *
        (Ideal.absNorm (cubePart (Ideal.span {z})) : ℝ) ^ 3 :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ hcube)
    _ = Ideal.absNorm (Ideal.span {z}) := (extracted_norm_product _ hI).symm
    _ ≤ M := (hR z hzR).2

theorem full_element_dyadic_extraction {n : Type*} [Fintype n] [DecidableEq n]
    (R : Finset O) (hRne : R.Nonempty) (M N : ℝ)
    (hR : ∀ z ∈ R, z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (cols : n → Ideal O) (hinj : Function.Injective cols)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (coef : n → ℂ) :
    ∃ X Y : ℝ, 1 ≤ X ∧ 1 ≤ Y ∧ X * Y ^ 2 ≤ M ∧
      (∑ z ∈ R, ‖∑ j, coef j * elementCharacter (cols j) (hcols j).1.2 z‖ ^ 2) ≤
        (192 * 128 ^ 2 : ℝ) *
          (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ) ^ 2 *
          (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) *
          min (Y * sieveNorm (2 * X) N) (X * sieveNorm (2 * Y) N) *
          ∑ j, ‖coef j‖ ^ 2 := by
  let J := Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
    Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1)
  let active : Finset J := Finset.univ.filter (fun j => (extractionBin R M j).Nonempty)
  let E : O → ℝ := fun z => ‖∑ j, coef j * elementCharacter (cols j) (hcols j).1.2 z‖ ^ 2
  let b : J → ℝ := fun j => ∑ z ∈ extractionBin R M j, E z
  have hactive : active.Nonempty := by
    obtain ⟨z, hz⟩ := hRne
    refine ⟨extractionLabel M z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨z, Finset.mem_filter.mpr ⟨hz, rfl⟩⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image active b hactive
  have hjne : (extractionBin R M j).Nonempty := (Finset.mem_filter.mp hj).2
  have hbnonneg : 0 ≤ b j := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsum : (∑ z ∈ R, E z) ≤ (Fintype.card J : ℝ) * b j := by
    rw [sum_extractionBins R M E]
    calc
      _ ≤ ∑ k : J, b j := by
        apply Finset.sum_le_sum
        intro k hk
        by_cases hka : k ∈ active
        · exact hmax k hka
        · have hempty : extractionBin R M k = ∅ := by
            have hh : ¬ (extractionBin R M k).Nonempty := by
              simpa only [active, Finset.mem_filter, Finset.mem_univ, true_and] using hka
            exact Finset.not_nonempty_iff_eq_empty.mp hh
          simpa only [hempty, Finset.sum_empty] using hbnonneg
      _ = _ := by simp
  let X := CanonicalQuadraticSieve.divisorDyadicScale j.1.val
  let Y := CanonicalQuadraticSieve.divisorDyadicScale j.2.val
  have hX : 1 ≤ X := CanonicalQuadraticSieve.divisorDyadicScale_ge_one _
  have hY : 1 ≤ Y := CanonicalQuadraticSieve.divisorDyadicScale_ge_one _
  have hXY : X * Y ^ 2 ≤ M := extractionBin_scale_product R M hR j hjne
  refine ⟨X, Y, hX, hY, hXY, ?_⟩
  have hb := full_element_dyadic_block_bound (extractionBin R M j)
    (fun z hz => (hR z (Finset.mem_filter.mp hz).1).1) M X Y N hX hY hXY
    (fun z hz => (extractionBin_bounds R M hR j z hz).1)
    (fun z hz => (extractionBin_bounds R M hR j z hz).2)
    (fun z hz => (hR z (Finset.mem_filter.mp hz).1).2) cols hinj hcols coef
  calc
    _ ≤ (Fintype.card J : ℝ) * b j := hsum
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
    _ = _ := by
      simp only [J, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

end
end SevenEighths.CubicSieve

end OAI

end Source509

/- Original source: OAI/NumberTheory/DirichletL/Descent/Marks.lean; sha256: c532c5c180a77984acb6aaae8b602846bcf41222276cfe6c0125b335bba30a64 -/
section Source510
namespace OAI

namespace SevenEighths.InverseMoment

open scoped BigOperators

noncomputable section

variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def primeSlot (L : Finset ι) (a : ι → ℂ) (A : Finset ι) : ℂ :=
  ∑ p ∈ L, if p ∈ A then a p else 0

def primeMark (I : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) : ℂ := ∏ i ∈ I, primeSlot (L i) (a i) A

omit [DecidableEq σ] in
@[simp] theorem primeMark_empty (L : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) : primeMark ∅ L a A = 1 := by
  simp [primeMark]

theorem primeMark_eq_tuple_sum (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    primeMark I L a A = ∑ p ∈ I.pi L,
      ∏ i ∈ I.attach, if p i.1 i.2 ∈ A then a i.1 (p i.1 i.2) else 0 := by
  exact Finset.prod_sum I L (fun i p => if p ∈ A then a i p else 0)

theorem primeSlot_priority (L A B : Finset ι) (a : ι → ℂ) :
    primeSlot L a (A ∪ B) = primeSlot L a A + primeSlot L a (B \ A) := by
  unfold primeSlot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hA : p ∈ A <;> by_cases hB : p ∈ B <;> simp [hA, hB]

theorem primeMark_priority (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A B : Finset ι) :
    primeMark I L a (A ∪ B) =
      ∑ J ∈ I.powerset, primeMark J L a A * primeMark (I \ J) L a (B \ A) := by
  unfold primeMark
  simp_rw [primeSlot_priority]
  exact Finset.prod_add _ _ I

theorem primeSlot_residual_list (L A B : Finset ι) (a : ι → ℂ) :
    primeSlot L a (B \ A) = primeSlot (L \ A) a B := by
  simp only [primeSlot, Finset.sum_ite_mem]
  congr 1
  ext p
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  tauto

omit [DecidableEq σ] in
theorem primeMark_residual_lists (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A B : Finset ι) :
    primeMark I L a (B \ A) = primeMark I (fun i => L i \ A) a B := by
  unfold primeMark
  apply Finset.prod_congr rfl
  intro i hi
  exact primeSlot_residual_list _ _ _ _

theorem primeSlot_norm_le (L A : Finset ι) (a : ι → ℂ)
    (ha : ∀ p ∈ L, ‖a p‖ ≤ 1) :
    ‖primeSlot L a A‖ ≤ ((L ∩ A).card : ℝ) := by
  simp only [primeSlot, Finset.sum_ite_mem]
  apply (norm_sum_le _ _).trans
  calc
    ∑ p ∈ L ∩ A, ‖a p‖ ≤ ∑ p ∈ L ∩ A, (1 : ℝ) :=
      Finset.sum_le_sum fun p hp => ha p (Finset.mem_inter.mp hp).1
    _ = _ := by simp

omit [DecidableEq σ] in
theorem primeMark_norm_le_divisor_count (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι)
    (hL : (I : Set σ).PairwiseDisjoint L)
    (ha : ∀ i ∈ I, ∀ p ∈ L i, ‖a i p‖ ≤ 1) :
    ‖primeMark I L a A‖ ≤ (2 : ℝ) ^ A.card := by
  have hdis : (I : Set σ).PairwiseDisjoint (fun i => L i ∩ A) := by
    intro i hi j hj hij
    exact (hL hi hj hij).mono (Finset.inter_subset_left) (Finset.inter_subset_left)
  have hcard : (∑ i ∈ I, (L i ∩ A).card) ≤ A.card := by
    rw [← Finset.card_biUnion hdis]
    apply Finset.card_le_card
    intro p hp
    obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_inter.mp hp).2
  calc
    ‖primeMark I L a A‖ = ∏ i ∈ I, ‖primeSlot (L i) (a i) A‖ := by
      exact norm_prod _ _
    _ ≤ ∏ i ∈ I, ((L i ∩ A).card : ℝ) := by
      exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
        (fun i hi => primeSlot_norm_le _ _ _ (ha i hi))
    _ ≤ ∏ i ∈ I, (2 : ℝ) ^ (L i ∩ A).card := by
      apply Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _)
      intro i hi
      exact_mod_cast (Nat.le_of_lt (L i ∩ A).card.lt_two_pow_self)
    _ = (2 : ℝ) ^ (∑ i ∈ I, (L i ∩ A).card) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ (2 : ℝ) ^ A.card := pow_le_pow_right₀ (by norm_num) hcard

end

end SevenEighths.InverseMoment

end OAI

end Source510

/- Original source: OAI/NumberTheory/DirichletL/Descent/Overlap.lean; sha256: a897c61cde304bad337851945d5dd1f47c75d80aaa8f2519cb65d5da31fc6166 -/
section Source511
namespace OAI

namespace SevenEighths.InverseMoment

open UniqueFactorizationMonoid

section Moebius

variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]

theorem moebius_squarefree_sq {P : M} (hP : Squarefree P) :
    moebius P ^ 2 = 1 := by
  rw [hP.moebius_eq, ← pow_mul, mul_comm _ 2, pow_mul]
  norm_num

theorem moebius_overlap_recovery {n P : M} (hnP : IsRelPrime n P)
    (hP : Squarefree P) : moebius n = moebius (n * P) * moebius P := by
  rw [hnP.moebius_mul, mul_assoc, ← pow_two, moebius_squarefree_sq hP, mul_one]

theorem moebius_character_overlap (ψ : M →* ℂ) {j n₀ P₀ : M}
    (hjn : IsRelPrime j n₀) (hnP : IsRelPrime n₀ P₀) (hP : Squarefree P₀) :
    (moebius (j * n₀) : ℂ) * ψ (j * n₀) * ψ (j * P₀) =
      (moebius j : ℂ) * (moebius P₀ : ℂ) * (moebius (n₀ * P₀) : ℂ) *
        ψ j ^ 2 * ψ (n₀ * P₀) := by
  have hμ : (moebius n₀ : ℂ) = (moebius (n₀ * P₀) : ℂ) * (moebius P₀ : ℂ) := by
    exact_mod_cast moebius_overlap_recovery hnP hP
  rw [hjn.moebius_mul, Int.cast_mul, map_mul, map_mul, map_mul, hμ]
  ring

theorem hybrid_mask_quotients {k P c R r : M}
    (hk : Squarefree k) (hP : Squarefree P) (hc : Squarefree c)
    (hPc : IsRelPrime P c) (hRk : R ∣ k) (hrk : r ∣ k)
    (hRP : R ∣ P) (hrc : r ∣ c) :
    ∃ k' P' c' : M,
      k = (R * r) * k' ∧ P = R * P' ∧ c = r * c' ∧
      IsRelPrime R r ∧ IsRelPrime k' (R * r) ∧
      IsRelPrime P' R ∧ IsRelPrime c' r ∧
      Squarefree k' ∧ Squarefree P' ∧ Squarefree c' := by
  have hRr : IsRelPrime R r := (hPc.of_dvd_left hRP).of_dvd_right hrc
  obtain ⟨k', hk'⟩ := hRr.mul_dvd hRk hrk
  obtain ⟨P', hP'⟩ := hRP
  obtain ⟨c', hc'⟩ := hrc
  have hks : Squarefree ((R * r) * k') := hk' ▸ hk
  have hPs : Squarefree (R * P') := hP' ▸ hP
  have hcs : Squarefree (r * c') := hc' ▸ hc
  obtain ⟨hkrel, _, hksf⟩ := squarefree_mul_iff.mp hks
  obtain ⟨hPrel, _, hPsf⟩ := squarefree_mul_iff.mp hPs
  obtain ⟨hcrel, _, hcsf⟩ := squarefree_mul_iff.mp hcs
  exact ⟨k', P', c', hk', hP', hc', hRr, hkrel.symm,
    hPrel.symm, hcrel.symm, hksf, hPsf, hcsf⟩

end Moebius

theorem inverse_eq_square_of_fourth_eq {z : ℂ} (hz : z ^ 4 = z) :
    z⁻¹ = z ^ 2 := by
  by_cases hzero : z = 0
  · simp [hzero]
  have hcube : z ^ 3 = 1 := by
    apply mul_left_cancel₀ hzero
    calc
      z * z ^ 3 = z ^ 4 := by ring
      _ = z := hz
      _ = z * 1 := by ring
  calc
    z⁻¹ = z⁻¹ * z ^ 3 := by rw [hcube, mul_one]
    _ = z ^ 2 := by field_simp

theorem inverse_cube_square_eq_sixth {z : ℂ} (h : z ^ 6 = 0 ∨ z ^ 6 = 1) :
    ((z ^ 3)⁻¹) ^ 2 = z ^ 6 := by
  rw [← inv_pow, ← pow_mul]
  norm_num
  rcases h with h | h <;> rw [h] <;> norm_num

theorem inverse_square_cube_mask {M : Type*} [Monoid M]
    (ψ : M →* ℂ) (n b : M) (h : ψ b ^ 6 = 0 ∨ ψ b ^ 6 = 1) :
    (ψ (n * b ^ 3))⁻¹ ^ 2 = (ψ n)⁻¹ ^ 2 * ψ b ^ 6 := by
  rw [map_mul, map_pow, mul_inv_rev, mul_pow, inverse_cube_square_eq_sixth h]
  ring

theorem overlap_scalar_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖z ^ 2‖ ≤ 1 := by
  rw [norm_pow]
  simpa using pow_le_pow_left₀ (norm_nonneg z) hz 2

end SevenEighths.InverseMoment

end OAI

end Source511

/- Original source: OAI/NumberTheory/DirichletL/Descent/IdealMasks.lean; sha256: f5ead07118118f452efb4ab516a1f19317b1dba32845ad5e4c1f9f4c880156e0 -/
section Source512
namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid IdealMobiusDivisorSum

theorem prime_mem_support_iff_dvd (P A : Ideal ActualEisensteinCubic.O)
    (hP : Prime P) (hA : A ≠ 0) :
    P ∈ IdealMobiusDivisorSum.primeSupport A ↔ P ∣ A := by
  simp only [IdealMobiusDivisorSum.primeSupport, Multiset.mem_toFinset,
    UniqueFactorizationMonoid.mem_normalizedFactors_iff hA, hP, true_and]

theorem ideal_primeMark_eq_divisibility {σ : Type*} [DecidableEq σ]
    (I : Finset σ) (L : σ → Finset (Ideal ActualEisensteinCubic.O))
    (a : σ → Ideal ActualEisensteinCubic.O → ℂ)
    (hL : ∀ i ∈ I, ∀ P ∈ L i, Prime P)
    (A : Ideal ActualEisensteinCubic.O) (hA : A ≠ 0) :
    primeMark I L a (IdealMobiusDivisorSum.primeSupport A) =
      ∏ i ∈ I, ∑ P ∈ L i, if P ∣ A then a i P else 0 := by
  unfold primeMark primeSlot
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro P hP
  simp only [prime_mem_support_iff_dvd P A (hL i hi P hP) hA]

theorem ideal_primeSupport_mul_cube (n b : Ideal ActualEisensteinCubic.O)
    (hn : n ≠ 0) (hb : b ≠ 0) :
    IdealMobiusDivisorSum.primeSupport (n * b ^ 3) =
      IdealMobiusDivisorSum.primeSupport n ∪ IdealMobiusDivisorSum.primeSupport b := by
  simp only [IdealMobiusDivisorSum.primeSupport,
    normalizedFactors_mul hn (pow_ne_zero 3 hb), normalizedFactors_pow,
    Multiset.toFinset_add]
  congr 1
  ext P
  simp

theorem ideal_whole_mark_priority {σ : Type*} [DecidableEq σ]
    (I : Finset σ) (L : σ → Finset (Ideal ActualEisensteinCubic.O))
    (a : σ → Ideal ActualEisensteinCubic.O → ℂ)
    (n b : Ideal ActualEisensteinCubic.O) (hn : n ≠ 0) (hb : b ≠ 0) :
    primeMark I L a (IdealMobiusDivisorSum.primeSupport (n * b ^ 3)) =
      ∑ J ∈ I.powerset,
        primeMark J L a (IdealMobiusDivisorSum.primeSupport n) *
        primeMark (I \ J) L a
          (IdealMobiusDivisorSum.primeSupport b \ IdealMobiusDivisorSum.primeSupport n) := by
  rw [ideal_primeSupport_mul_cube n b hn hb]
  exact primeMark_priority _ _ _ _ _

theorem ideal_primeMark_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {σ : Type*} [DecidableEq σ]
      (I : Finset σ) (L : σ → Finset (Ideal ActualEisensteinCubic.O))
      (a : σ → Ideal ActualEisensteinCubic.O → ℂ),
      (I : Set σ).PairwiseDisjoint L →
      (∀ i ∈ I, ∀ P ∈ L i, ‖a i P‖ ≤ 1) →
      ∀ A : Ideal ActualEisensteinCubic.O, A ≠ 0 →
        ‖primeMark I L a (IdealMobiusDivisorSum.primeSupport A)‖ ≤
          C * (Ideal.absNorm A : ℝ) ^ ε := by
  obtain ⟨C, hC, hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro σ _ I L a hL ha A hA
  exact (primeMark_norm_le_divisor_count I L a _ hL ha).trans (hb A hA)

theorem ideal_coprime_mobius (K P : Ideal ActualEisensteinCubic.O) (hK : K ≠ 0) :
    (if IsCoprime K P then (1 : ℂ) else 0) =
      ∑ R ∈ idealDivisors K, if R ∣ P then (moebius R : ℂ) else 0 := by
  let G := K ⊔ P
  have hG : G ≠ 0 := by
    intro hz
    apply hK
    exact le_antisymm (show K ≤ 0 from hz ▸ (le_sup_left : K ≤ G)) bot_le
  have hdiv : (idealDivisors K).filter (fun R => R ∣ P) = idealDivisors G := by
    ext R
    simp only [Finset.mem_filter, mem_idealDivisors hK, mem_idealDivisors hG,
      Ideal.dvd_iff_le, G, sup_le_iff]
  rw [← Finset.sum_filter, hdiv, sum_moebius_divisors G hG]
  simp only [Ideal.isCoprime_iff_sup_eq, G]

theorem idealZeroMask_primary_indicator
    (D B : Ideal ActualEisensteinCubic.O) (hD : D ≠ 0)
    (hB : CompletedGauss.primaryGenerator B ≠ 0) :
    CanonicalQuadraticSieve.idealZeroMask D (CompletedGauss.primaryGenerator B) =
      if IsCoprime B D then 1 else 0 := by
  have he : Ideal.span {CompletedGauss.primaryGenerator B} =
      Ideal.span {ConcretePrimeRowBridge.idealGenerator B} := by
    rw [(CompletedGauss.primaryGenerator_spec B hB).1,
      ConcretePrimeRowBridge.span_idealGenerator]
  rw [CanonicalQuadraticSieve.idealZeroMask_span_eq D _ _ he,
    CanonicalQuadraticSieve.idealZeroMask_generator_eq_indicator D B hD]

theorem hybrid_quadratic_square_mask
    (k n b c m h t : Ideal ActualEisensteinCubic.O)
    (hk : CanonicalQuadraticSieve.Admissible k)
    (hn : n = c * m) (hb : b = (c * h) * t ^ 2)
    (hct : CompletedGauss.primaryGenerator (c * t) ≠ 0) :
    CanonicalQuadraticSieve.quadraticRow k (CompletedGauss.primaryGenerator (n * b)) =
      (if IsCoprime k (c * t) then 1 else 0) *
        CanonicalQuadraticSieve.quadraticRow k (CompletedGauss.primaryGenerator (m * h)) := by
  have he : n * b = (c * t) ^ 2 * (m * h) := by rw [hn, hb]; ring
  rw [he, CanonicalQuadraticSieve.canonical_quadraticRow_primary_squarefree k hk,
    idealZeroMask_primary_indicator k (c * t) hk.1 hct]
  rw [isCoprime_comm]

theorem hybrid_double_mask_mobius
    (k P c : Ideal ActualEisensteinCubic.O) (hk : k ≠ 0) :
    (if IsCoprime k (P * c) then (1 : ℂ) else 0) =
      ∑ R ∈ idealDivisors k, ∑ r ∈ idealDivisors k,
        if R ∣ P ∧ r ∣ c then (moebius R : ℂ) * (moebius r : ℂ) else 0 := by
  have hsplit : (if IsCoprime k (P * c) then (1 : ℂ) else 0) =
      (if IsCoprime k P then 1 else 0) * (if IsCoprime k c then 1 else 0) := by
    simp only [IsCoprime.mul_right_iff]
    by_cases hP : IsCoprime k P <;> by_cases hc : IsCoprime k c <;> simp [hP, hc]
  rw [hsplit, ideal_coprime_mobius k P hk, ideal_coprime_mobius k c hk,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro R hR
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hP : R ∣ P <;> by_cases hc : r ∣ c <;> simp [hP, hc]

theorem hybrid_column_decomposition
    (n b : Ideal ActualEisensteinCubic.O) (hn : Squarefree n) (hb : b ≠ 0) :
    ∃ c m h t : Ideal ActualEisensteinCubic.O,
      n = c * m ∧ b = (c * h) * t ^ 2 ∧
      Squarefree c ∧ Squarefree m ∧ Squarefree h ∧
      IsRelPrime c m ∧ IsRelPrime c h ∧ IsCoprime m h ∧ t ≠ 0 := by
  let g := QuadraticSquarefreeKernel.squarefreePart b
  let t := QuadraticSquarefreeKernel.squarePart b
  let c := gcd n g
  let m := CanonicalQuadraticSieve.idealQuotient c n
  let h := CanonicalQuadraticSieve.idealQuotient c g
  have hg : Squarefree g := QuadraticSquarefreeKernel.squarefree_squarefreePart b
  have hcn : c ∣ n := gcd_dvd_left n g
  have hcg : c ∣ g := gcd_dvd_right n g
  have hc : c ≠ 0 := ne_zero_of_dvd_ne_zero hn.ne_zero hcn
  have hnm : n = c * m := (CanonicalQuadraticSieve.idealQuotient_mul hcn).symm
  have hgh : g = c * h := (CanonicalQuadraticSieve.idealQuotient_mul hcg).symm
  have hbgt : b = g * t ^ 2 := by
    rw [mul_comm]
    exact (QuadraticSquarefreeKernel.squarePart_sq_mul_squarefreePart b).symm
  obtain ⟨hcm, hcs, hms⟩ := squarefree_mul_iff.mp (hnm ▸ hn)
  obtain ⟨hch, _, hhs⟩ := squarefree_mul_iff.mp (hgh ▸ hg)
  have hmh : IsCoprime m h :=
    (CanonicalQuadraticSieve.gcd_eq_iff_quotient_coprime c n g hc hcn hcg).mp rfl
  exact ⟨c, m, h, t, hnm, by rw [hbgt, hgh], hcs, hms, hhs, hcm, hch, hmh,
    QuadraticSquarefreeKernel.squarePart_ne_zero hb⟩

theorem ideal_product_fiber_card
    (s t : Finset (Ideal ActualEisensteinCubic.O))
    (J : Ideal ActualEisensteinCubic.O) (hJ : J ≠ 0) :
    (((s ×ˢ t).filter (fun p => p.1 * p.2 = J)).card) ≤ (idealDivisors J).card :=
  CanonicalQuadraticSieve.product_fiber_card (s ×ˢ t) J hJ

theorem scaled_product_fiber_card
    (pairs : Finset (Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O))
    (B J : Ideal ActualEisensteinCubic.O) (hJ : J ≠ 0) :
    ((pairs.filter (fun p => p.2 * (B * p.1) = J)).card) ≤ (idealDivisors J).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    apply (mem_idealDivisors hJ).mpr
    refine ⟨p.2 * B, ?_⟩
    rw [← (Finset.mem_filter.mp hp).2]
    ring
  · intro p hp q hq hpq
    have hep := (Finset.mem_filter.mp hp).2
    have heq := (Finset.mem_filter.mp hq).2
    have hBm : B * p.1 ≠ 0 := by
      intro hz
      apply hJ
      rw [← hep, hz, mul_zero]
    apply Prod.ext hpq
    apply mul_right_cancel₀ hBm
    rw [hep, hpq, heq]

end

end SevenEighths.InverseMoment

end OAI

end Source512

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/Gcd.lean; sha256: 5b55cbddd422dc616d489815c5a04cf30f4f6f5a6fd9dfb09b30c26ebb0097e9 -/
section Source513
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve (idealQuotient totalQuotient gcdPool)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def cubicRow (I : Ideal O) (z : O) : ℂ :=
  eisEmbedding (CubicJacobiGlobal.idealSymbol I z)

lemma cubicRow_mul (I J : Ideal O) (z : O) :
    cubicRow (I * J) z = cubicRow I z * cubicRow J z := by
  simp only [cubicRow, ← CanonicalRowCompletion.idealRowHom_square, map_mul, mul_pow]

lemma cubicRow_square_eq_star (I : Ideal O) (z : O) :
    cubicRow I z ^ 2 = star (cubicRow I z) :=
  square_eq_star_of_fourth_eq _ (idealSymbol_fourth I z)

lemma cubicRow_common_mask (D : Ideal O) (hD : primaryGenerator D ≠ 0) (z : O) :
    star (cubicRow D z) * cubicRow D z =
      if IsCoprime D (Ideal.span {z}) then 1 else 0 := by
  rw [← cubicRow_square_eq_star]
  calc
    _ = cubicRow D z ^ 3 := by ring
    _ = _ := idealSymbol_cube_mask D z hD

lemma cubicRow_common_mobius (D : Ideal O) (hD : primaryGenerator D ≠ 0) (z : O) :
    star (cubicRow D z) * cubicRow D z =
      ∑ E ∈ IdealMobiusDivisorSum.idealDivisors D,
        if E ∣ Ideal.span {z} then (UniqueFactorizationMonoid.moebius E : ℂ) else 0 := by
  rw [cubicRow_common_mask D hD z]
  exact SevenEighths.InverseMoment.ideal_coprime_mobius D _ (primaryGenerator_ne_zero_ideal D hD)

lemma cubic_admissible_of_dvd {I D : Ideal O} (hI : Admissible I) (hD : D ∣ I) :
    Admissible D := by
  refine ⟨hI.1.squarefree_of_dvd hD, ?_⟩
  obtain ⟨J, he⟩ := hD
  have hp := hI.2
  rw [he, primaryGenerator_mul] at hp
  exact (mul_ne_zero_iff.mp hp).1

lemma cubic_admissible_quotient {I D : Ideal O} (hI : Admissible I) (hD : D ∣ I) :
    Admissible (idealQuotient D I) :=
  cubic_admissible_of_dvd hI (CanonicalQuadraticSieve.idealQuotient_dvd hD)

lemma cubicRow_divisor_factor (D I : Ideal O) (hDI : D ∣ I) (z : O) :
    cubicRow I z = cubicRow D z * cubicRow (idealQuotient D I) z := by
  conv_lhs => rw [← CanonicalQuadraticSieve.idealQuotient_mul hDI]
  exact cubicRow_mul _ _ _

def cubicGcdTerm {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (z : O) (j k : n) : ℂ :=
  if gcd (cols j) (cols k) = D then
    star (cubicRow (cols j) z * a j) * (cubicRow (cols k) z * a k) else 0

theorem cubicGcdTerm_eq_quotient {n : Type*}
    (D : Ideal O) (hD : D ≠ 0) (cols : n → Ideal O)
    (a : n → ℂ) (z : O) (j k : n) :
    cubicGcdTerm D cols a z j k =
      (star (cubicRow D z) * cubicRow D z) *
      (if IsCoprime (totalQuotient D (cols j)) (totalQuotient D (cols k)) then
        star (cubicRow (totalQuotient D (cols j)) z * (if D ∣ cols j then a j else 0)) *
          (cubicRow (totalQuotient D (cols k)) z * (if D ∣ cols k then a k else 0)) else 0) := by
  by_cases hj : D ∣ cols j
  · by_cases hk : D ∣ cols k
    · simp only [cubicGcdTerm, totalQuotient, ite_eq_left hj, ite_eq_left hk]
      rw [← CanonicalQuadraticSieve.gcd_eq_iff_quotient_coprime D (cols j) (cols k) hD hj hk]
      by_cases hg : gcd (cols j) (cols k) = D
      · rw [ite_eq_left hg, ite_eq_left hg, cubicRow_divisor_factor D _ hj,
          cubicRow_divisor_factor D _ hk]
        simp only [star_mul]
        ring
      · simp only [ite_eq_right hg, mul_zero]
    · have hg : gcd (cols j) (cols k) ≠ D := by
        intro he
        exact hk (he ▸ gcd_dvd_right (cols j) (cols k))
      simp only [cubicGcdTerm, ite_eq_right hg]
      simp [hk]
  · have hg : gcd (cols j) (cols k) ≠ D := by
      intro he
      exact hj (he ▸ gcd_dvd_left (cols j) (cols k))
    simp only [cubicGcdTerm, ite_eq_right hg]
    simp [hj]

theorem cubic_weighted_energy_eq_gcd_blocks {n : Type*} [Fintype n]
    (R : Finset O) (w : O → ℂ) (cols : n → Ideal O) (a : n → ℂ) :
    (∑ z ∈ R, w z * (‖∑ j, cubicRow (cols j) z * a j‖ ^ 2 : ℝ)) =
      ∑ D ∈ gcdPool cols, ∑ z ∈ R, w z * ∑ j, ∑ k, cubicGcdTerm D cols a z j k := by
  have hp (z : O) (j k : n) :
      (∑ D ∈ gcdPool cols, cubicGcdTerm D cols a z j k) =
      star (cubicRow (cols j) z * a j) * (cubicRow (cols k) z * a k) := by
    rw [Finset.sum_eq_single (gcd (cols j) (cols k))]
    · simp only [cubicGcdTerm, ite_true]
    · intro D hD hne
      exact ite_eq_right (Ne.symm hne)
    · exact fun h => (h (CanonicalQuadraticSieve.mem_gcdPool cols j k)).elim
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  conv_rhs => arg 2; ext j; rw [Finset.sum_comm]
  simp_rw [hp]
  simpa only [Complex.ofReal_pow] using CoprimeSieveOperator.square_norm_sum
    (fun j => cubicRow (cols j) z * a j)

end
end SevenEighths.CubicSieve

end OAI

end Source513

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/Gauss.lean; sha256: 0993c4e0f408c698e53d890b27aba44ce8c36e3ea9b0b2fda6b8fcc7a058ff98 -/
section Source514
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def cubicQuotientCharacter (I : Ideal O) (hI : Admissible I) : MulChar (O ⧸ I) ℂ where
  toFun := CompletedGauss.cubicRow I hI.2
  map_one' := by simp [CompletedGauss.cubicRow]
  map_mul' x y := by simp only [CompletedGauss.cubicRow, map_mul, Finset.prod_mul_distrib]
  map_nonunit' x hx := by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [CubicEisenstein.cubicRow_eq_idealSymbol I hI.2 hI.1]
    have hcop : ¬ IsCoprime I (Ideal.span {z}) := by
      simpa only [CubicEisenstein.isUnit_quotient_iff_sup, Ideal.isCoprime_iff_sup_eq] using hx
    have hc := idealSymbol_cube_mask I z hI.2
    rw [ite_eq_right hcop] at hc
    exact (eq_zero_of_pow_eq_zero hc)

@[simp] lemma cubicQuotientCharacter_mk (I : Ideal O) (hI : Admissible I) (z : O) :
    cubicQuotientCharacter I hI (Ideal.Quotient.mk I z) = cubicRow I z :=
  CubicEisenstein.cubicRow_eq_idealSymbol I hI.2 hI.1 z

lemma cubicQuotientCharacter_cube (I : Ideal O) (hI : Admissible I) :
    cubicQuotientCharacter I hI ^ 3 = 1 := by
  apply DFunLike.ext
  intro x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), cubicQuotientCharacter_mk, cubicRow,
    idealSymbol_cube_mask I z hI.2]
  have hu : IsUnit (Ideal.Quotient.mk I z) ↔ IsCoprime I (Ideal.span {z}) := by
    rw [CubicEisenstein.isUnit_quotient_iff_sup, Ideal.isCoprime_iff_sup_eq]
  by_cases h : IsUnit (Ideal.Quotient.mk I z)
  · rw [ite_eq_left (hu.mp h), MulChar.one_apply h]
  · rw [ite_eq_right (fun hcop => h (hu.mpr hcop)), MulChar.map_nonunit _ h]

lemma cubicQuotientCharacter_neg_one (I : Ideal O) (hI : Admissible I) :
    cubicQuotientCharacter I hI (-1) = 1 := by
  have h3 := congrArg (fun χ : MulChar (O ⧸ I) ℂ => χ (-1)) (cubicQuotientCharacter_cube I hI)
  rw [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), MulChar.one_apply (isUnit_neg_one)] at h3
  have h2 : cubicQuotientCharacter I hI (-1) ^ 2 = 1 := by rw [← map_pow]; norm_num
  calc
    _ = cubicQuotientCharacter I hI (-1) ^ 2 * cubicQuotientCharacter I hI (-1) := by rw [h2, one_mul]
    _ = cubicQuotientCharacter I hI (-1) ^ 3 := by ring
    _ = 1 := h3

def quotientCharacterTransport {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (χ : MulChar S ℂ) : MulChar R ℂ where
  toFun x := χ (e x)
  map_one' := by simp
  map_mul' x y := by simp only [map_mul]
  map_nonunit' x hx := MulChar.map_nonunit χ (fun h => hx (by simpa using h.map e.symm.toMonoidHom))

def principalCubicCharacter (I : Ideal O) (hI : Admissible I) :
    MulChar (O ⧸ Ideal.span {primaryGenerator I}) ℂ :=
  quotientCharacterTransport (Ideal.quotEquivOfEq (primaryGenerator_spec I hI.2).1)
    (cubicQuotientCharacter I hI)

@[simp] lemma principalCubicCharacter_mk (I : Ideal O) (hI : Admissible I) (z : O) :
    principalCubicCharacter I hI (Ideal.Quotient.mk _ z) = cubicRow I z := by
  change cubicQuotientCharacter I hI ((Ideal.quotEquivOfEq (primaryGenerator_spec I hI.2).1) (Ideal.Quotient.mk _ z)) = _
  rw [Ideal.quotEquivOfEq_mk, cubicQuotientCharacter_mk]

lemma principalCubicCharacter_neg_one (I : Ideal O) (hI : Admissible I) :
    principalCubicCharacter I hI (-1) = 1 := by
  change cubicQuotientCharacter I hI ((Ideal.quotEquivOfEq (primaryGenerator_spec I hI.2).1) (-1)) = 1
  rw [map_neg, map_one, cubicQuotientCharacter_neg_one]

lemma gaussTwo_eq_gaussSum (I : Ideal O) (hI : Admissible I) :
    let : Finite (O ⧸ Ideal.span {primaryGenerator I}) := finite_quotient_span hI.2
    let : Fintype (O ⧸ Ideal.span {primaryGenerator I}) := Fintype.ofFinite _
    gaussTwo I hI.2 = gaussSum (principalCubicCharacter I hI)
      (eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
        (primaryGenerator I) hI.2) / (‖eisEmbedding (primaryGenerator I)‖ : ℂ) := by
  dsimp only [gaussTwo, gaussSum, principalCubicCharacter, quotientCharacterTransport, cubicQuotientCharacter]
  congr 1

lemma gaussSum_inverse_of_even {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (ψ : AddChar R ℂ) (heven : χ (-1) = 1) :
    gaussSum χ⁻¹ ψ = star (gaussSum χ ψ) := by
  rw [star_gaussSum_eq]
  have hh : χ⁻¹ (-1) = 1 := by rw [← MulChar.star_apply', heven, star_one]
  have h := gaussSum_mulShift χ⁻¹ ψ (-1 : Rˣ)
  rw [Units.coe_neg_one, ← ψ.inv_mulShift, hh, one_mul] at h
  exact h.symm

lemma cubic_pair_cross_phase (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) :
    (principalCubicCharacter I hI)⁻¹ (Ideal.Quotient.mk _ (primaryGenerator J)) *
      principalCubicCharacter J hJ (Ideal.Quotient.mk _ (primaryGenerator I)) = 1 := by
  let : Finite (O ⧸ Ideal.span {primaryGenerator I}) := finite_quotient_span hI.2
  rw [← MulChar.star_apply', principalCubicCharacter_mk, principalCubicCharacter_mk]
  change star (idealKernel I J) * idealKernel J I = 1
  rw [← idealKernel_reciprocity I J hI.2 hJ.2]
  change star (cubicRow I (primaryGenerator J)) * cubicRow I (primaryGenerator J) = 1
  rw [cubicRow_common_mask I hI.2, (primaryGenerator_spec J hJ.2).1, ite_eq_left hcop]

def cubicPairGauss (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) : ℂ := by
  let a := primaryGenerator I
  let b := primaryGenerator J
  let : Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := finite_quotient_product hI.2 hJ.2
  let : Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := Fintype.ofFinite _
  exact (∑ x : O ⧸ (Ideal.span {a}) * (Ideal.span {b}),
    (principalCubicCharacter I hI)⁻¹ (Ideal.Quotient.factor Ideal.mul_le_left x) *
      principalCubicCharacter J hJ (Ideal.Quotient.factor Ideal.mul_le_right x) *
      eisTraceProdChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates a b hI.2 hJ.2 x) /
      ((‖eisEmbedding a‖ : ℂ) * (‖eisEmbedding b‖ : ℂ))

theorem cubicPairGauss_separation (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) :
    cubicPairGauss I J hI hJ = star (gaussTwo I hI.2) * gaussTwo J hJ.2 := by
  let : Finite (O ⧸ Ideal.span {primaryGenerator I}) := finite_quotient_span hI.2
  let : Fintype (O ⧸ Ideal.span {primaryGenerator I}) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {primaryGenerator J}) := finite_quotient_span hJ.2
  let : Fintype (O ⧸ Ideal.span {primaryGenerator J}) := Fintype.ofFinite _
  let : Finite (O ⧸ (Ideal.span {primaryGenerator I}) * (Ideal.span {primaryGenerator J})) :=
    finite_quotient_product hI.2 hJ.2
  let : Fintype (O ⧸ (Ideal.span {primaryGenerator I}) * (Ideal.span {primaryGenerator J})) := Fintype.ofFinite _
  have hc : IsCoprime (Ideal.span {primaryGenerator I}) (Ideal.span {primaryGenerator J}) := by
    rwa [(primaryGenerator_spec I hI.2).1, (primaryGenerator_spec J hJ.2).1]
  dsimp only [cubicPairGauss]
  rw [gauss_sum_actual_O ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
    (primaryGenerator I) (primaryGenerator J) hI.2 hJ.2 hc,
    cubic_pair_cross_phase I J hI hJ hcop, one_mul,
    gaussSum_inverse_of_even _ _ (principalCubicCharacter_neg_one I hI),
    gaussTwo_eq_gaussSum I hI, gaussTwo_eq_gaussSum J hJ]
  have halg (a b : ℂ) (x y : ℝ) :
      star a * b / ((x : ℂ) * (y : ℂ)) = star (a / (x : ℂ)) * (b / (y : ℂ)) := by
    simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]
    ring
  exact halg _ _ _ _

end
end SevenEighths.CubicSieve

end OAI

end Source514

/- Original source: OAI/NumberTheory/DirichletL/Detector/PairPhase.lean; sha256: 3dcd070ab0321a560b03c04e3790cc467f41bfa57739bae9a4f5f78316aa0533 -/
section Source515
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates CompletedGauss
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

def sexticPair (p q : O) : ℂ :=
  idealRowHom q (Ideal.span {p}) * idealRowHom p (Ideal.span {q})

theorem sexticPair_cube (p q : O) (hp : Prime p) (hq : Prime q)
    (hprimaryP : goodLambda ^ 2 ∣ p - 1) (hprimaryQ : goodLambda ^ 2 ∣ q - 1)
    (hsP : Supported (Ideal.span {p})) (hsQ : Supported (Ideal.span {q}))
    (hcop : IsCoprime (Ideal.span {p} : Ideal O) (Ideal.span {q})) :
    sexticPair p q ^ 3 = reciprocitySign p q := by
  have hr : idealRowHom q (Ideal.span {p}) =
      reciprocitySign p q * idealRowHom p (Ideal.span {q}) :=
    idealRowHom_prime_reciprocity p q hp hq hprimaryP hprimaryQ hsP hsQ
  have h6 := idealRowHom_sixth_mask p (Ideal.span {q}) hsQ
  rw [idealRowHom_argument_pow _ _ _ hsQ, ite_eq_left hcop.symm] at h6
  have h2 := reciprocitySign_sq p q (supported_residue_odd p hsP) (supported_residue_odd q hsQ)
  calc
    sexticPair p q ^ 3 = reciprocitySign p q ^ 3 * idealRowHom p (Ideal.span {q}) ^ 6 := by
      unfold sexticPair
      rw [hr]
      ring
    _ = reciprocitySign p q := by rw [h6, mul_one, pow_succ, h2, one_mul]

theorem completed_pair_phase (p q : O) (hp : Prime p) (hq : Prime q)
    (hprimaryP : goodLambda ^ 2 ∣ p - 1) (hprimaryQ : goodLambda ^ 2 ∣ q - 1)
    (hsP : Supported (Ideal.span {p})) (hsQ : Supported (Ideal.span {q}))
    (hcop : IsCoprime (Ideal.span {p} : Ideal O) (Ideal.span {q})) (e f l k : ℕ) :
    sexticPair p q ^ ((e + 3 * l) * (f + 3 * k)) / sexticPair p q ^ (e * f) =
      reciprocitySign p q ^ (e * k + f * l + l * k) := by
  have h3 := sexticPair_cube p q hp hq hprimaryP hprimaryQ hsP hsQ hcop
  have h2 := reciprocitySign_sq p q (supported_residue_odd p hsP) (supported_residue_odd q hsQ)
  have hr : reciprocitySign p q ≠ 0 := by intro h; rw [h, zero_pow (by decide)] at h2; norm_num at h2
  have hz : sexticPair p q ≠ 0 := by intro h; rw [h, zero_pow (by decide)] at h3; exact hr h3.symm
  have hexp : (e + 3 * l) * (f + 3 * k) = e * f + 3 * (e * k + f * l + 3 * l * k) := by ring
  rw [hexp, pow_add, pow_mul (sexticPair p q) 3 (e * k + f * l + 3 * l * k),
    h3, mul_div_cancel_left₀ _ (pow_ne_zero _ hz)]
  have htail : e * k + f * l + 3 * l * k = (e * k + f * l + l * k) + 2 * (l * k) := by ring
  rw [htail, pow_add, pow_mul (reciprocitySign p q) 2 (l * k), h2, one_pow, mul_one]

end SevenEighths.ProbePhase
end

end OAI

end Source515

/- Original source: OAI/NumberTheory/DirichletL/Detector/CubicGaussCRT.lean; sha256: b1624a922827f505a97694bc59e702ac994d1d28b06d24ff7d0efa8c416cf192 -/
section Source516
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open CompletedGauss ConcreteTraceCRT CubicEisenstein GaussianShiftedPartition
open CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier CenteredMomentFirstPoisson
local notation "O" => ActualEisensteinCubic.O

lemma gaussTwo_eq_elementFourier (I : Ideal O) (hI : CubicSieve.Admissible I) :
    gaussTwo I hI.2 =
      elementFourier (primaryGenerator I) hI.2 (CubicSieve.cubicRow I) 1 /
        (‖eisEmbedding (primaryGenerator I)‖:ℂ) := by
  let := finite_quotient_span hI.2
  let : Fintype (Residue (primaryGenerator I)) := Fintype.ofFinite _
  rw [CubicSieve.gaussTwo_eq_gaussSum I hI]
  unfold gaussSum elementFourier
  rw [tsum_fintype]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  have hc := CubicSieve.principalCubicCharacter_mk I hI (representative (primaryGenerator I) x)
  rw [representative_spec] at hc
  rw [hc]
  simp only [map_one, one_mul]
  rfl

lemma residueGauss_principalCubicCharacter (I : Ideal O) (hI : CubicSieve.Admissible I)
    [Fintype (Residue (primaryGenerator I))] :
    residueGauss (primaryGenerator I) hI.2 (CubicSieve.principalCubicCharacter I hI) 1 =
      elementFourier (primaryGenerator I) hI.2 (CubicSieve.cubicRow I) 1 := by
  simp only [residueGauss, elementFourier, tsum_fintype, map_one, one_mul]
  apply Finset.sum_congr rfl
  intro x hx
  have hc := CubicSieve.principalCubicCharacter_mk I hI (representative (primaryGenerator I) x)
  rw [representative_spec] at hc
  rw [hc]

theorem gaussTwo_coprime_product (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hcop : IsCoprime I J) :
    gaussTwo (I*J) hIJ.2 =
      (CubicSieve.cubicRow I (primaryGenerator J) * CubicSieve.cubicRow J (primaryGenerator I)) *
      gaussTwo I hI.2 * gaussTwo J hJ.2 := by
  let a := primaryGenerator I
  let b := primaryGenerator J
  have hc : IsCoprime a b := by
    rw [← Ideal.isCoprime_span_singleton_iff]
    simpa only [a,b,(primaryGenerator_spec I hI.2).1,(primaryGenerator_spec J hJ.2).1] using hcop
  let := finite_quotient_span hI.2
  let := finite_quotient_span hJ.2
  let := finite_quotient_span (mul_ne_zero hI.2 hJ.2)
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (a*b)) := Fintype.ofFinite _
  have he := coprime_character_fourier a b hI.2 hJ.2 hc
    (CubicSieve.principalCubicCharacter I hI) (CubicSieve.principalCubicCharacter J hJ) 1
  simp only [map_one] at he
  have hfour : elementFourier (a*b) (mul_ne_zero hI.2 hJ.2)
      (CubicSieve.cubicRow (I*J)) 1 =
      (CubicSieve.cubicRow I b * CubicSieve.cubicRow J a) *
        elementFourier a hI.2 (CubicSieve.cubicRow I) 1 *
        elementFourier b hJ.2 (CubicSieve.cubicRow J) 1 := by
    unfold elementFourier
    rw [tsum_fintype, tsum_fintype, tsum_fintype]
    calc
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        obtain ⟨m,rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [CubicSieve.cubicRow_mul]
        have hi : CubicSieve.cubicRow I (representative (a*b) (Ideal.Quotient.mk _ m)) =
            CubicSieve.cubicRow I m := by
          rw [← CubicSieve.principalCubicCharacter_mk I hI, ← CubicSieve.principalCubicCharacter_mk I hI]
          congr 1
          apply Ideal.Quotient.eq.mpr
          have hx := Ideal.Quotient.eq.mp (representative_spec (a*b) (Ideal.Quotient.mk _ m))
          exact Ideal.mem_span_singleton.mpr ((dvd_mul_right a b).trans (Ideal.mem_span_singleton.mp hx))
        have hj : CubicSieve.cubicRow J (representative (a*b) (Ideal.Quotient.mk _ m)) =
            CubicSieve.cubicRow J m := by
          rw [← CubicSieve.principalCubicCharacter_mk J hJ, ← CubicSieve.principalCubicCharacter_mk J hJ]
          congr 1
          apply Ideal.Quotient.eq.mpr
          have hx := Ideal.Quotient.eq.mp (representative_spec (a*b) (Ideal.Quotient.mk _ m))
          exact Ideal.mem_span_singleton.mpr ((dvd_mul_left b a).trans (Ideal.mem_span_singleton.mp hx))
        rw [hi,hj]
        simp only [frequencyReduction_mk, map_one, one_mul]
        rw [CubicSieve.principalCubicCharacter_mk I hI m, CubicSieve.principalCubicCharacter_mk J hJ m]
      _ = _ := he
      _ = _ := by
        rw [CubicSieve.principalCubicCharacter_mk I hI b,
          CubicSieve.principalCubicCharacter_mk J hJ a,
          residueGauss_principalCubicCharacter I hI, residueGauss_principalCubicCharacter J hJ]
        simp only [elementFourier, tsum_fintype]
        rfl
  rw [gaussTwo_eq_elementFourier (I*J) hIJ, gaussTwo_eq_elementFourier I hI,
    gaussTwo_eq_elementFourier J hJ]
  have hgen : primaryGenerator (I*J)=a*b := primaryGenerator_mul I J
  rw [elementFourier_congr _ (a*b) hIJ.2 (mul_ne_zero hI.2 hJ.2) _ 1 hgen, hfour]
  rw [hgen, map_mul, norm_mul, Complex.ofReal_mul]
  ring

theorem gaussTwo_coprime_product_sextic (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hcop : IsCoprime I J) :
    gaussTwo (I*J) hIJ.2 =
      ProbePhase.sexticPair (primaryGenerator I) (primaryGenerator J)^2 *
        gaussTwo I hI.2 * gaussTwo J hJ.2 := by
  rw [gaussTwo_coprime_product I J hI hJ hIJ hcop]
  simp only [CubicSieve.cubicRow, ← idealRowHom_square, ProbePhase.sexticPair,
    (primaryGenerator_spec I hI.2).1, (primaryGenerator_spec J hJ.2).1, mul_pow]

end SevenEighths.ProbePhysical
end

end OAI

end Source516

/- Original source: OAI/NumberTheory/DirichletL/Detector/CompletedCRTPhase.lean; sha256: 3532a0269977bf70e2ca9c233cbfedf27964e5e2fce414a6c9f6857326acc220 -/
section Source517
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates CompletedGauss CubicEisenstein
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

lemma reciprocitySign_star (a b : O) : star (reciprocitySign a b)=reciprocitySign a b := by
  simp only [reciprocitySign, star_intCast]

theorem completed_cubic_pair_cancel (p q : O) (hp : Prime p) (hq : Prime q)
    (hprimaryP : goodLambda^2∣p-1) (hprimaryQ : goodLambda^2∣q-1)
    (hsP : Supported (Ideal.span {p})) (hsQ : Supported (Ideal.span {q}))
    (hcop : IsCoprime (Ideal.span {p} : Ideal O) (Ideal.span {q}))
    (e f l k : ℕ) :
    sexticPair p q ^ ((e+3*l)*(f+3*k)) * sexticPair p q ^ (2*e*f) *
      star (reciprocitySign (p^(e+3*l)) (q^(f+3*k))) = 1 := by
  have hpodd := supported_residue_odd p hsP
  have hqodd := supported_residue_odd q hsQ
  have h3 := sexticPair_cube p q hp hq hprimaryP hprimaryQ hsP hsQ hcop
  have h2 := reciprocitySign_sq p q hpodd hqodd
  rw [reciprocitySign_star, reciprocitySign_pow_left p _ (odd_residue_pow q hqodd _) _,
    reciprocitySign_pow_right p q hpodd, ← pow_mul, ← pow_add]
  have hexp : (e+3*l)*(f+3*k)+2*e*f = 3*(e*f+e*k+f*l+3*l*k) := by ring
  rw [hexp, pow_mul, h3, ← pow_add]
  have hsum : e*f+e*k+f*l+3*l*k+(f+3*k)*(e+3*l) =
      2*(e*f+2*e*k+2*f*l+6*l*k) := by ring
  rw [hsum, pow_mul, h2, one_pow]

lemma sexticPair_mul_left (a b c : O) :
    sexticPair (a*b) c = sexticPair a c * sexticPair b c := by
  simp only [sexticPair, ← Ideal.span_singleton_mul_span_singleton, map_mul,
    idealRowHom_argument_mul]
  ring

lemma sexticPair_mul_right (a b c : O) :
    sexticPair a (b*c) = sexticPair a b * sexticPair a c := by
  simp only [sexticPair, ← Ideal.span_singleton_mul_span_singleton, map_mul,
    idealRowHom_argument_mul]
  ring

lemma sexticPair_cube_left (a b : O) : sexticPair (a^3) b=sexticPair a b^3 := by
  rw [show a^3=a*a*a by ring, sexticPair_mul_left, sexticPair_mul_left]
  ring

lemma sexticPair_cube_right (a b : O) : sexticPair a (b^3)=sexticPair a b^3 := by
  rw [show b^3=b*b*b by ring, sexticPair_mul_right, sexticPair_mul_right]
  ring

theorem sexticPair_cube_supported (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpa : goodLambda^2∣a-1) (hpb : goodLambda^2∣b-1) (hcop : IsCoprime a b) :
    sexticPair a b^3 = reciprocitySign a b := by
  have hr : idealRowHom b (Ideal.span {a}) =
      reciprocitySign a b * idealRowHom a (Ideal.span {b}) :=
    idealRowHom_primary_reciprocity a b hpa hpb ha hb
  have hc : IsCoprime (Ideal.span {b}:Ideal O) (Ideal.span {a}) := by
    exact (Ideal.isCoprime_span_singleton_iff b a).mpr hcop.symm
  have h6 := idealRowHom_sixth_mask a (Ideal.span {b}) hb
  rw [idealRowHom_argument_pow _ _ _ hb, ite_eq_left hc] at h6
  have h2 := reciprocitySign_sq a b (supported_residue_odd a ha) (supported_residue_odd b hb)
  calc
    _ = reciprocitySign a b^3 * idealRowHom a (Ideal.span {b})^6 := by
      unfold sexticPair
      rw [hr]
      ring
    _ = _ := by rw [h6,mul_one,pow_succ,h2,one_mul]

theorem completed_cubic_cross_cancel (c n d m : O)
    (hc : Supported (Ideal.span {c})) (hn : Supported (Ideal.span {n}))
    (hd : Supported (Ideal.span {d})) (hm : Supported (Ideal.span {m}))
    (hpc : goodLambda^2∣c-1) (hpn : goodLambda^2∣n-1)
    (hpd : goodLambda^2∣d-1) (hpm : goodLambda^2∣m-1)
    (hcd : IsCoprime c d) (hcm : IsCoprime c m)
    (hnd : IsCoprime n d) (hnm : IsCoprime n m) :
    sexticPair (c*n^3) (d*m^3) * sexticPair c d^2 *
      star (reciprocitySign (c*n^3) (d*m^3)) = 1 := by
  have hcd3 := sexticPair_cube_supported c d hc hd hpc hpd hcd
  have hcm3 := sexticPair_cube_supported c m hc hm hpc hpm hcm
  have hnd3 := sexticPair_cube_supported n d hn hd hpn hpd hnd
  have hnm3 := sexticPair_cube_supported n m hn hm hpn hpm hnm
  have hRnm := reciprocitySign_sq n m (supported_residue_odd n hn) (supported_residue_odd m hm)
  have he : sexticPair (c*n^3) (d*m^3)*sexticPair c d^2 =
      reciprocitySign (c*n^3) (d*m^3) := by
    calc
      _ = sexticPair c d^3 * sexticPair c m^3 * sexticPair n d^3 *
          (sexticPair n m^3)^3 := by
        rw [sexticPair_mul_left, sexticPair_mul_right, sexticPair_mul_right,
          sexticPair_cube_left, sexticPair_cube_left, sexticPair_cube_right,
          sexticPair_cube_right]
        ring
      _ = reciprocitySign c d * reciprocitySign c m * reciprocitySign n d * reciprocitySign n m := by
        rw [hcd3,hcm3,hnd3,hnm3,pow_succ,hRnm,one_mul]
      _ = _ := by
        rw [reciprocitySign_mul_left, reciprocitySign_mul_right, reciprocitySign_mul_right,
          reciprocitySign_cube_right c m (supported_residue_odd c hc) (supported_residue_odd m hm),
          reciprocitySign_symm (n^3) d,
          reciprocitySign_cube_right d n (supported_residue_odd d hd) (supported_residue_odd n hn),
          reciprocitySign_symm d n,
          reciprocitySign_cube_right (n^3) m (odd_residue_pow n (supported_residue_odd n hn) 3)
            (supported_residue_odd m hm), reciprocitySign_symm (n^3) m,
          reciprocitySign_cube_right m n (supported_residue_odd m hm) (supported_residue_odd n hn),
          reciprocitySign_symm m n]
        ring
  rw [he,reciprocitySign_star,←pow_two]
  exact reciprocitySign_sq _ _
    (by simpa only [ActualEisensteinCoordinates.residue_mul] using
      (EisensteinEPrimaryPhase.odd_mul _ _ (supported_residue_odd c hc)
        (odd_residue_pow n (supported_residue_odd n hn) 3)))
    (by simpa only [ActualEisensteinCoordinates.residue_mul] using
      (EisensteinEPrimaryPhase.odd_mul _ _ (supported_residue_odd d hd)
        (odd_residue_pow m (supported_residue_odd m hm) 3)))

end SevenEighths.ProbePhase
end

end OAI

end Source517

/- Original source: OAI/NumberTheory/DirichletL/Detector/CompletedCoefficient.lean; sha256: 73c24a04fa469f891a63a491a6d8afaa52249cf0b4ab2cf3eb0c4b99a9585648 -/
section Source518
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein ProbePhase
local notation "O" => ActualEisensteinCubic.O

lemma supported_completed (c n : O) (hc : Supported (Ideal.span {c}))
    (hn : Supported (Ideal.span {n})) : Supported (Ideal.span {c*n^3}) := by
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow]
  apply (supported_mul_iff _ _).mpr
  refine ⟨hc,?_⟩
  have hn2 := (supported_mul_iff _ _).mpr ⟨hn,hn⟩
  have hn3 := (supported_mul_iff _ _).mpr ⟨hn2,hn⟩
  simpa only [pow_succ, pow_zero, one_mul] using hn3

lemma primary_completed (c n : O) (hc : goodLambda^2∣c-1)
    (hn : goodLambda^2∣n-1) : goodLambda^2∣c*n^3-1 := by
  have h := dvd_add (dvd_mul_of_dvd_left hc (n^3))
    (dvd_mul_of_dvd_left hn (n^2+n+1))
  convert h using 1 ; ring

def correctedFiniteCoefficient (I : Ideal O) (hI : primaryGenerator I≠0)
    (A s : O) (hA : A≠0) (H : O) : ℂ :=
  gaussTwo I hI * star (G A) * reciprocityCoefficient A s hA H

theorem correctedFiniteCoefficient_product (I J : Ideal O)
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
    correctedFiniteCoefficient (I*J) hIJ.2 (A*B) (s*r) (mul_ne_zero hA hB) H =
      correctedFiniteCoefficient I hI.2 A s hA H * correctedFiniteCoefficient J hJ.2 B r hB H := by
  dsimp only
  let c := primaryGenerator I
  let d := primaryGenerator J
  let A := c*n^3
  let B := d*m^3
  have hAs := supported_completed c n hc hn
  have hBs := supported_completed d m hd hm
  have hAB : IsCoprime A B := hcop.of_mul_left_left.of_mul_right_left
  have hnA : n∣A := by refine ⟨c*n^2,?_⟩; dsimp only [A]; ring
  have hmB : m∣B := by refine ⟨d*m^2,?_⟩; dsimp only [B]; ring
  have hcA : c∣A := dvd_mul_right c (n^3)
  have hdB : d∣B := dvd_mul_right d (m^3)
  have hcd : IsCoprime c d := (hAB.of_isCoprime_of_dvd_left hcA).of_isCoprime_of_dvd_right hdB
  have hcm : IsCoprime c m := (hAB.of_isCoprime_of_dvd_left hcA).of_isCoprime_of_dvd_right hmB
  have hnd : IsCoprime n d := (hAB.of_isCoprime_of_dvd_left hnA).of_isCoprime_of_dvd_right hdB
  have hnm : IsCoprime n m := (hAB.of_isCoprime_of_dvd_left hnA).of_isCoprime_of_dvd_right hmB
  have hphase := completed_cubic_cross_cancel c n d m hc hn hd hm hpc hpn hpd hpm hcd hcm hnd hnm
  change sexticPair A B * sexticPair c d^2 * star (reciprocitySign A B)=1 at hphase
  change gaussTwo (I*J) hIJ.2 * star (G (A*B)) *
      reciprocityCoefficient (A*B) (s*r) _ H =
    (gaussTwo I hI.2 * star (G A) * reciprocityCoefficient A s _ H) *
    (gaussTwo J hJ.2 * star (G B) * reciprocityCoefficient B r _ H)
  rw [gaussTwo_coprime_product_sextic I J hI hJ hIJ hIJcop,
    G_mul A B (supported_residue_odd A hAs) (supported_residue_odd B hBs),
    reciprocityCoefficient_product A B s r hAs hBs hs hr
      (primary_completed c n hpc hpn) (primary_completed d m hpd hpm) hps hpr hcop H]
  simp only [star_mul]
  change (sexticPair c d^2 * gaussTwo I hI.2 * gaussTwo J hJ.2) *
    (star (reciprocitySign A B)*(star (G B)*star (G A))) *
    (sexticPair A B * reciprocityCoefficient A s _ H * reciprocityCoefficient B r _ H) = _
  calc
    _ = (sexticPair A B * sexticPair c d^2 * star (reciprocitySign A B)) *
      ((gaussTwo I hI.2 * star (G A) * reciprocityCoefficient A s _ H) *
       (gaussTwo J hJ.2 * star (G B) * reciprocityCoefficient B r _ H)) := by ring
    _ = _ := by rw [hphase,one_mul]

end SevenEighths.ProbePhysical
end

end OAI

end Source518

/- Original source: OAI/NumberTheory/DirichletL/Detector/CalibrationSupport.lean; sha256: 3de800afc83570e01c6583d5fe4847b3e63887d3b9f936dd824cff5e314fe224 -/
section Source519
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O

theorem calibrationForSet_coprime_iff (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (a : O) : IsCoprime (calibrationForSet S hS).generator a ↔ ∀ P ∈ S, a ∉ P := by
  rw [← Ideal.isCoprime_span_singleton_iff, calibrationForSet_span, IsCoprime.prod_left_iff]
  constructor
  · intro h P hP
    let : P.IsMaximal := hS P hP
    exact (SixthPowerAverage.prime_coprime_span_iff P a).mp (h P hP)
  · intro h P hP
    let : P.IsMaximal := hS P hP
    exact (SixthPowerAverage.prime_coprime_span_iff P a).mpr (h P hP)

theorem calibrationForSet_coprime_of_excluded (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, P.IsMaximal) (a : O)
    (hmask : ∀ P ∈ S, ¬P ∣ Ideal.span {a}) :
    IsCoprime (calibrationForSet S hS).generator a := by
  apply (calibrationForSet_coprime_iff S hS a).mpr
  intro P hP ha
  apply hmask P hP
  exact Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha))

theorem source_rowCoefficient_apply (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (s : O) (hs : Supported (Ideal.span {s})) (m a : O)
    (ha : Supported (Ideal.span {a})) (hmask : ∀ P ∈ S, ¬P ∣ Ideal.span {a}) :
    rowCoefficient η (calibrationForSet S hS).Xi s hs m a =
      HeckeFamily.elementCoeff η a * ((calibrationForSet S hS).Xi a)⁻¹ *
        sexticReciprocityPhase a s * idealRowHom m (Ideal.span {a}) :=
  calibrated_rowCoefficient_apply η (calibrationForSet S hS) s hs m a ha
    (calibrationForSet_coprime_of_excluded S hS a hmask)

end SevenEighths.ProbePhysical
end

end OAI

end Source519
