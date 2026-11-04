import NumericalPolynomialMiddle
import NumericalCorrectionProfile
import NumericalStrongLogGate

/-! Paying the compact-strip polynomial correction from a fixed fraction of
the hat error. The logarithmic gate is explicit in the statement; this module
does not yet choose the global separator for the mixed induction. -/

open scoped Classical BigOperators
namespace ChenEffective
variable [profile : CorrectionProfile]
open Real Set Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

noncomputable def polynomialCorrectionWeight : ℝ := CorrectionProfile.weight

theorem polynomialCorrectionWeight_pos : 0 < polynomialCorrectionWeight := CorrectionProfile.positive

theorem polynomialCorrectionWeight_small : polynomialCorrectionWeight ≤ 1 := CorrectionProfile.le_one

theorem polynomialCorrectionWeight_inverse (hweight : Real.exp (-1000 : ℝ) ≤ polynomialCorrectionWeight) :
    polynomialCorrectionWeight⁻¹ ≤ Real.exp 1000 := by
  have hh := (inv_le_inv₀ polynomialCorrectionWeight_pos (Real.exp_pos (-1000 : ℝ))).mpr hweight
  simpa only [← Real.exp_neg, neg_neg] using hh

omit profile in
theorem default_correction_lower : Real.exp (-1000 : ℝ) ≤
    polynomialCorrectionWeight (profile := defaultCorrectionProfile) := by
  change Real.exp (-1000 : ℝ) ≤ 1
  exact Real.exp_le_one_iff.mpr (by norm_num)
omit profile in
theorem polynomial_compact_hat_floor {H : Section13HatLayers}
    (hH : Section13HatContract H 2) {D s : ℝ} (hD : 1 < D)
    (n : ℕ) (hs : 2 ≤ s) (hs16 : s ≤ 16) :
    Real.exp (-896 : ℝ) ≤ errorEnvelope H n D 16 s := by
  have hs0 : 0 < s := by linarith only [hs]
  have hLD : 0 < Real.log D := Real.log_pos hD
  have hlog : Real.log (6 * s) ≤ 7 := by
    calc
      _ ≤ Real.log ((2 : ℝ) ^ 7) := Real.log_le_log (by positivity) (by norm_num; linarith only [hs16])
      _ = 7 * Real.log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ 7 := by linarith only [Real.log_two_lt_d9]
  have hlog0 : 0 ≤ Real.log (6 * s) := Real.log_nonneg (by linarith only [hs])
  have hbound : 8 * s * Real.log (6 * s) ≤ 896 := by
    nlinarith only [mul_le_mul_of_nonneg_right hs16 hlog0,
      mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ 16 by norm_num)]
  have hhat : Real.exp (-896 : ℝ) ≤ H.T (ErrorSign.ofDepth n) s :=
    (Real.exp_le_exp.mpr (by linarith only [hbound])).trans
      (numerical_hat_lower_profile hH _ hs)
  have hP : 1 ≤ (1 + s ^ (16 : ℝ) / Real.log D) ^ s :=
    Real.one_le_rpow (le_add_of_nonneg_right (by positivity :
      0 ≤ s ^ (16 : ℝ) / Real.log D)) hs0.le
  have hT0 : 0 ≤ H.T (ErrorSign.ofDepth n) s := (hH.positive _ _ hs0).le
  unfold errorEnvelope Section13HatLayers.kappaHat
  norm_num only [sub_self, zero_add, Real.rpow_one]
  have hmult : 1 ≤ (1 + s ^ (16 : ℝ) / Real.log D) ^ s * s := by
    nlinarith only [mul_le_mul_of_nonneg_right hP hs0.le, hs]
  exact hhat.trans (by nlinarith only [mul_le_mul_of_nonneg_right hmult hT0])

/-- A small correction can be charged to 1/(100 sigma) of the hat budget.
The result has no recursion depth parameter. -/
theorem polynomial_compact_correction_payment {L σ E : ℝ}
    (hL : 0 < L) (hσ : 0 < σ)
    (hgate : σ * L ^ (-(1 / 8 : ℝ)) ≤ Real.exp (-940 : ℝ))
    (hE : Real.exp (-896 : ℝ) ≤ E) :
    polynomialCorrectionWeight * L ^ (-(5 / 8 : ℝ)) ≤
      E * L ^ (-(1 / 2 : ℝ)) / (100 * σ) := by
  have h100 : (100 : ℝ) ≤ Real.exp 44 := by
    have hh := Real.pow_div_factorial_le_exp (44 : ℝ) (by norm_num) 2
    norm_num [Nat.factorial] at hh
    linarith only [hh]
  have hb : 100 * polynomialCorrectionWeight ≤ Real.exp 44 :=
    (show 100 * polynomialCorrectionWeight ≤ (100 : ℝ) by nlinarith only [polynomialCorrectionWeight_small]).trans h100
  have hleft : (100 * polynomialCorrectionWeight) * (σ * L ^ (-(1 / 8 : ℝ))) ≤ E := by
    calc
      _ ≤ Real.exp 44 * Real.exp (-940 : ℝ) := mul_le_mul hb hgate (by positivity) (Real.exp_pos _).le
      _ = Real.exp (-896 : ℝ) := by rw [← Real.exp_add]; norm_num
      _ ≤ E := hE
  have hh := mul_le_mul_of_nonneg_right hleft
    (Real.rpow_nonneg hL.le (-(1 / 2 : ℝ)))
  apply (le_div_iff₀ (by positivity : 0 < 100 * σ)).mpr
  have heq : L ^ (-(5 / 8 : ℝ)) = L ^ (-(1 / 8 : ℝ)) * L ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hL]
    norm_num
  rw [heq]
  nlinarith only [hh]

omit profile in
/-- A uniform coarse bound for the discrete polynomial kernel on the whole
Case-I strip, before the sharper high-coordinate contraction is used. -/
theorem numerical_polynomial_transport_coarse
    {S : BoundingSieve} {D z w s σ K : ℝ}
    (hD : 1 < D) (hz2 : 2 ≤ z) (hw2 : 2 ≤ w) (hwz : w ≤ z)
    (hz : z = D ^ (1 / s)) (hw : w = D ^ (1 / σ))
    (hs : 2 ≤ s) (hsσ : s ≤ σ)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K)
    (hlevel : 288 * K ^ 2 ≤ Real.log w) :
    suzukiLemmaEightSevenPrimeSum S D w z z polynomialTransportKernel ≤ 3 / 8 := by
  have hs0 : 0 < s := by linarith only [hs]
  have hs1 : 1 ≤ s - 1 := by linarith only [hs]
  have hlog : 0 < Real.log w := Real.log_pos (by linarith only [hw2])
  have hratio : K ^ 2 / Real.log w ≤ 1 / 288 := by
    apply (div_le_iff₀ hlog).mpr
    linarith only [hlevel]
  have hcube : 1 ≤ (s - 1) ^ 3 := one_le_pow₀ hs1
  have hfour : 1 ≤ (s - 1) ^ 4 := one_le_pow₀ hs1
  have hi : (1 / s) * (∫ t in s..σ, polynomialTransportKernel t) ≤ 1 / 3 := by
    apply (polynomialTransportKernel_integral_bound hs0 hs hsσ).trans
    apply (div_le_iff₀ (by positivity : 0 < 3 * s * (s - 1) ^ 3)).mpr
    nlinarith only [mul_le_mul hs hcube (by norm_num : (0 : ℝ) ≤ 1) hs0.le]
  have hend : (6 * K ^ 2 * polynomialTransportKernel s / Real.log w) * (s / s) ≤ 1 / 24 := by
    rw [div_self hs0.ne', mul_one, polynomialTransportKernel_eq hs]
    calc
      _ = 12 * (K ^ 2 / Real.log w) / (s - 1) ^ 4 := by ring
      _ ≤ 12 * (1 / 288 : ℝ) / (s - 1) ^ 4 := by gcongr
      _ ≤ _ := by apply (div_le_iff₀ (by positivity : 0 < (s - 1) ^ 4)).mpr; linarith only [hfour]
  have hh := numerical_polynomial_prime_transport hD hz2 hz2 hw2 hwz le_rfl
    hz hz hw hs hsσ hK hlocal
  exact hh.trans (by linarith only [hi, hend])

#print axioms polynomial_compact_correction_payment
#print axioms numerical_polynomial_transport_coarse
end ChenEffective
