import NumericalPolynomialTail
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma87DimensionOne
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Discrete transport of a polynomial correction

The coarse kernel `2/(t-1)^4` covers a logarithmic exponent at most one
when the recursive level has at least half the parent logarithm. Clamping
below two supplies the global continuity required by the production Lemma 8.7.
The estimates here are independent of depth. The high-coordinate estimate is
a strict contraction. The cubic Case-II estimate is a bounded transfer, not a
claim of contraction at the odd low strip.
-/

open scoped Classical BigOperators Interval
namespace ChenEffective
open Real Set MeasureTheory intervalIntegral
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple

set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable def polynomialTransportKernel (t : ℝ) : ℝ :=
  2 / (max 2 t - 1) ^ 4

theorem polynomialTransportKernel_eq {t : ℝ} (ht : 2 ≤ t) :
    polynomialTransportKernel t = 2 / (t - 1) ^ 4 := by
  rw [polynomialTransportKernel, max_eq_right ht]

theorem polynomialTransportKernel_continuous : Continuous polynomialTransportKernel := by
  unfold polynomialTransportKernel
  apply continuous_const.div (((continuous_const.max continuous_id).sub continuous_const).pow 4)
  intro t
  have hh := le_max_left (2 : ℝ) t
  apply pow_ne_zero 4
  change max 2 t - 1 ≠ 0
  linarith only [hh]

theorem polynomialTransportKernel_weighted_antitone {τ σ : ℝ} (hτ : 2 ≤ τ) :
    AntitoneOn (fun t => polynomialTransportKernel t * t) (Icc τ σ) := by
  intro x hx y hy hxy
  have hx2 : 2 ≤ x := hτ.trans hx.1
  have hy2 : 2 ≤ y := hτ.trans hy.1
  change polynomialTransportKernel y * y ≤ polynomialTransportKernel x * x
  rw [polynomialTransportKernel_eq hx2, polynomialTransportKernel_eq hy2]
  have hx1 : 0 < x - 1 := by linarith only [hx2]
  have hy1 : 0 < y - 1 := by linarith only [hy2]
  have hr : y / (y - 1) ≤ x / (x - 1) := by
    apply (div_le_div_iff₀ hy1 hx1).mpr
    nlinarith only [hxy]
  have hi : 1 / (y - 1) ^ 3 ≤ 1 / (x - 1) ^ 3 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hx1.le (by linarith only [hxy]) 3)
  have hh := mul_le_mul hr hi (by positivity : 0 ≤ 1 / (y - 1) ^ 3)
    (by positivity : 0 ≤ x / (x - 1))
  have heqx : 2 / (x - 1) ^ 4 * x = 2 * (x / (x - 1) * (1 / (x - 1) ^ 3)) := by
    field_simp
  have heqy : 2 / (y - 1) ^ 4 * y = 2 * (y / (y - 1) * (1 / (y - 1) ^ 3)) := by
    field_simp
  rw [heqx, heqy]
  linarith only [hh]

theorem polynomialTransportKernel_integral {τ σ : ℝ} (hτ : 2 ≤ τ) (hτσ : τ ≤ σ) :
    (∫ t in τ..σ, polynomialTransportKernel t) =
      2 / (3 * (τ - 1) ^ 3) - 2 / (3 * (σ - 1) ^ 3) := by
  have hderiv (t : ℝ) (ht : t ∈ uIcc τ σ) :
      HasDerivAt (fun u : ℝ => -(2 / 3 : ℝ) / (u - 1) ^ 3)
        (polynomialTransportKernel t) t := by
    have ht' : t ∈ Icc τ σ := by simpa only [uIcc_of_le hτσ] using ht
    have ht2 : 2 ≤ t := hτ.trans ht'.1
    have hne : t - 1 ≠ 0 := by linarith only [ht2]
    rw [polynomialTransportKernel_eq ht2]
    have hh := (hasDerivAt_const t (-(2 / 3 : ℝ))).div
      (((hasDerivAt_id t).sub_const 1).pow 3) (pow_ne_zero 3 hne)
    apply hh.congr_deriv
    dsimp
    field_simp [hne]
    ring
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (polynomialTransportKernel_continuous.intervalIntegrable τ σ)
  rw [hh]
  have hτne : τ - 1 ≠ 0 := by linarith only [hτ]
  have hσne : σ - 1 ≠ 0 := by linarith only [hτ, hτσ]
  field_simp [hτne, hσne]
  ring

theorem polynomialTransportKernel_integral_bound {s τ σ : ℝ}
    (hs : 0 < s) (hτ : 2 ≤ τ) (hτσ : τ ≤ σ) :
    (1 / s) * (∫ t in τ..σ, polynomialTransportKernel t) ≤
      2 / (3 * s * (τ - 1) ^ 3) := by
  rw [polynomialTransportKernel_integral hτ hτσ]
  have hnon : 0 ≤ 2 / (3 * (σ - 1) ^ 3) := by
    have : 0 < σ - 1 := by linarith only [hτ, hτσ]
    positivity
  have hh := mul_le_mul_of_nonneg_left
    (sub_le_self (2 / (3 * (τ - 1) ^ 3)) hnon) (by positivity : 0 ≤ 1 / s)
  apply hh.trans_eq
  field_simp

/-- A fixed strict contraction of the continuous inherited correction on the
high-coordinate strip. -/
theorem polynomialTransportKernel_high {s σ : ℝ} (hs : 16 ≤ s) (hsσ : s ≤ σ) :
    (1 / s) * (∫ t in s..σ, polynomialTransportKernel t) ≤ (5 / 6 : ℝ) / s ^ 4 := by
  have hs0 : 0 < s := by linarith only [hs]
  apply (polynomialTransportKernel_integral_bound hs0 (by linarith only [hs]) hsσ).trans
  have hsub : 0 ≤ s - 16 := by linarith only [hs]
  have hs1 : 0 < s - 1 := by linarith only [hs]
  have hpoly : 4 * s ^ 3 ≤ 5 * (s - 1) ^ 3 := by
    have hpos : 0 ≤ (s - 16) ^ 3 + 33 * (s - 16) ^ 2 + 303 * (s - 16) + 491 := by positivity
    nlinarith only [hpos]
  apply (div_le_div_iff₀ (by positivity : 0 < 3 * s * (s - 1) ^ 3)
    (by positivity : 0 < s ^ 4)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hpoly hs0.le]

/-- The cubic Case-II kernel has a uniform transfer bound. In particular its
estimate contains no factor depending on the number of recursive levels. -/
theorem polynomialTransportKernel_caseII {s σ : ℝ} (hs : 0 < s) (hσ : 3 ≤ σ) :
    (1 / s) * (∫ t in (3 : ℝ)..σ, polynomialTransportKernel t) ≤ 1 / (12 * s) := by
  have hh := polynomialTransportKernel_integral_bound hs (by norm_num : (2 : ℝ) ≤ 3) hσ
  norm_num only [sub_self, Nat.cast_ofNat, one_div, show (3 : ℝ) - 1 = 2 by norm_num] at hh
  convert hh using 1 <;> ring

/-- Production Lemma 8.7, specialized to the polynomial correction. -/
theorem numerical_polynomial_prime_transport
    {S : BoundingSieve} {D z v w s τ σ K : ℝ}
    (hD : 1 < D) (hz2 : 2 ≤ z) (hv2 : 2 ≤ v) (hw2 : 2 ≤ w)
    (hwv : w ≤ v) (hvz : v ≤ z)
    (hz : z = D ^ (1 / s)) (hv : v = D ^ (1 / τ)) (hw : w = D ^ (1 / σ))
    (hτ : 2 ≤ τ) (_hτσ : τ ≤ σ)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K) :
    suzukiLemmaEightSevenPrimeSum S D w v z polynomialTransportKernel ≤
      (1 / s) * (∫ t in τ..σ, polynomialTransportKernel t) +
        (6 * K ^ 2 * polynomialTransportKernel τ / Real.log w) * (τ / s) :=
  suzukiLemmaEightSevenDimensionOne hD hz2 hv2 hw2 hwv hvz hz hv hw
    polynomialTransportKernel_continuous (fun _ _ => by unfold polynomialTransportKernel; positivity)
    (polynomialTransportKernel_weighted_antitone hτ) hK hlocal

#print axioms polynomialTransportKernel_high
#print axioms polynomialTransportKernel_caseII
#print axioms numerical_polynomial_prime_transport
end ChenEffective
