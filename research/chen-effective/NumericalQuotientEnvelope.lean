import NumericalHatLower

namespace ChenEffective
open Real Set Filter MeasureTheory
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def quotientCoordinateCutoff (Q : ℕ) : ℕ := 1679616 * Q + 6
noncomputable def quotientEnvelopeLower (Q : ℕ) : ℝ :=
  min 1 (2 * compactHatLower (quotientCoordinateCutoff Q))

theorem quotientCoordinateCutoff_three (Q : ℕ) : 3 ≤ quotientCoordinateCutoff Q := by
  unfold quotientCoordinateCutoff
  omega

theorem quotientEnvelopeLower_pos (Q : ℕ) : 0 < quotientEnvelopeLower Q :=
  lt_min (by norm_num) (mul_pos (by norm_num)
    (compactHatLower_pos (quotientCoordinateCutoff_three Q)))

theorem numerical_error_envelope_large {H : Section13HatLayers}
    (hH : Section13HatContract H 2) {D Q : ℕ} (hD : 2 ≤ D)
    (hbudget : Real.log (D : ℝ) ≤ Q) (n : ℕ) {s : ℝ}
    (hs : (quotientCoordinateCutoff Q : ℝ) ≤ s) :
    1 ≤ errorEnvelope H n (D : ℝ) 16 s := by
  let L := Real.log (D : ℝ)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast (show 1 < D by omega))
  have hs3 : 3 ≤ s :=
    (show (3 : ℝ) ≤ (quotientCoordinateCutoff Q : ℕ) by
      exact_mod_cast quotientCoordinateCutoff_three Q).trans hs
  have hs2 : 2 ≤ s := by linarith only [hs3]
  have hs0 : 0 < s := by linarith only [hs3]
  have hlarge : (6 : ℝ) ^ (8 : ℕ) * L ≤ s := by
    have hh := mul_le_mul_of_nonneg_left hbudget (by norm_num : (0 : ℝ) ≤ 1679616)
    have hc : (quotientCoordinateCutoff Q : ℝ) = 1679616 * (Q : ℝ) + 6 := by
      simp only [quotientCoordinateCutoff, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [hc] at hs
    norm_num only [show (6 : ℝ) ^ (8 : ℕ) = 1679616 by norm_num]
    change 1679616 * L ≤ s
    linarith only [hs, hh]
  have hlog : 8 * Real.log 6 + Real.log L ≤ Real.log s := by
    have hh := Real.log_le_log (mul_pos (pow_pos (by norm_num) 8) hL) hlarge
    rw [Real.log_mul (by norm_num) hL.ne', Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    exact hh
  have hlogs0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith only [hs3])
  have harg : 0 < s ^ (16 : ℝ) / L := by positivity
  have hform : (s ^ (16 : ℝ) / L) ^ s * Real.exp (-8 * s * Real.log (6 * s)) =
      Real.exp (s * (8 * Real.log s - Real.log L - 8 * Real.log 6)) := by
    rw [Real.rpow_def_of_pos harg, Real.log_div (by positivity) hL.ne',
      Real.log_rpow hs0, Real.log_mul (by norm_num) hs0.ne', ← Real.exp_add]
    congr 1
    ring
  have hone : 1 ≤ (s ^ (16 : ℝ) / L) ^ s * Real.exp (-8 * s * Real.log (6 * s)) := by
    rw [hform]
    apply Real.one_le_exp_iff.mpr
    apply mul_nonneg hs0.le
    linarith only [hlog, hlogs0]
  have hpow : (s ^ (16 : ℝ) / L) ^ s ≤ (1 + s ^ (16 : ℝ) / L) ^ s :=
    Real.rpow_le_rpow harg.le (by linarith) hs0.le
  have hhat := numerical_hat_lower_profile hH (ErrorSign.ofDepth n) hs2
  have hprod := mul_le_mul hpow hhat (Real.exp_pos _).le
    (by positivity : 0 ≤ (1 + s ^ (16 : ℝ) / L) ^ s)
  have hH0 : 0 ≤ H.T (ErrorSign.ofDepth n) s := (hH.positive _ s hs0).le
  have hscale := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ s by linarith only [hs3])
    (show 0 ≤ (1 + s ^ (16 : ℝ) / L) ^ s * H.T (ErrorSign.ofDepth n) s by positivity)
  unfold errorEnvelope Section13HatLayers.kappaHat
  norm_num only [sub_self, zero_add, Real.rpow_one]
  change 1 ≤ (1 + s ^ (16 : ℝ) / L) ^ s * s * H.T (ErrorSign.ofDepth n) s
  nlinarith only [hone, hprod, hscale]

/-- All coordinates and all depths, with a numerical lower bound for every log budget. -/
theorem numerical_error_envelope_lower {H : Section13HatLayers}
    (hH : Section13HatContract H 2) {D Q : ℕ} (hD : 2 ≤ D)
    (hbudget : Real.log (D : ℝ) ≤ Q) (n : ℕ) {s : ℝ} (hs : 2 ≤ s) :
    quotientEnvelopeLower Q ≤ errorEnvelope H n (D : ℝ) 16 s := by
  by_cases hlarge : (quotientCoordinateCutoff Q : ℝ) ≤ s
  · exact (min_le_left _ _).trans (numerical_error_envelope_large hH hD hbudget n hlarge)
  · have hsmall : s ≤ (quotientCoordinateCutoff Q : ℝ) := le_of_not_ge hlarge
    have hhat := numerical_hat_compact hH (quotientCoordinateCutoff_three Q) (ErrorSign.ofDepth n) hs hsmall
    have hs0 : 0 < s := by linarith only [hs]
    have hL : 0 < Real.log (D : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < D by omega))
    have hb : 1 ≤ (1 + s ^ (16 : ℝ) / Real.log (D : ℝ)) ^ s :=
      Real.one_le_rpow (by
        have hh : 0 ≤ s ^ (16 : ℝ) / Real.log (D : ℝ) := by positivity
        linarith only [hh]) hs0.le
    have he := compactHatLower_pos (quotientCoordinateCutoff_three Q)
    have hT0 : 0 ≤ H.T (ErrorSign.ofDepth n) s := (hH.positive _ s hs0).le
    have hh := mul_le_mul hb hs (by norm_num : (0 : ℝ) ≤ 2)
      (by positivity : 0 ≤ (1 + s ^ (16 : ℝ) / Real.log (D : ℝ)) ^ s)
    have hh' := mul_le_mul hh hhat he.le (by positivity)
    unfold errorEnvelope Section13HatLayers.kappaHat
    norm_num only [sub_self, zero_add, Real.rpow_one]
    apply (min_le_right _ _).trans
    nlinarith only [hh']

#print axioms numerical_error_envelope_lower
end ChenEffective
