import NumericalHatCompact

namespace ChenEffective
open Real Set Filter MeasureTheory
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- A coarse explicit lower profile, sufficient for the fixed-quotient d=16 branch. -/
theorem numerical_hat_lower_profile {H : Section13HatLayers}
    (hH : Section13HatContract H 2) (sign : ErrorSign) {s : ℝ} (hs : 2 ≤ s) :
    Real.exp (-8 * s * Real.log (6 * s)) ≤ H.T sign s := by
  let m : ℕ := max 3 ⌈s⌉₊
  have hm3 : 3 ≤ m := le_max_left _ _
  have hsm : s ≤ (m : ℝ) := (Nat.le_ceil s).trans (by exact_mod_cast le_max_right 3 ⌈s⌉₊)
  have hm : (m : ℝ) ≤ 2 * s := by
    dsimp [m]
    rw [Nat.cast_max, max_le_iff]
    norm_num only [Nat.cast_ofNat]
    refine ⟨by linarith only [hs], ?_⟩
    have hh := Nat.ceil_lt_add_one (show 0 ≤ s by linarith only [hs])
    linarith only [hh, hs]
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm3
  have hm0 : (0 : ℝ) < m := by linarith only [hmR]
  have hs0 : 0 < s := by linarith only [hs]
  have hA1 : 1 ≤ Real.log (6 * s) := one_le_log_three.trans
    (Real.log_le_log (by norm_num) (by linarith only [hs]))
  have hA0 : 0 ≤ Real.log (6 * s) := by linarith only [hA1]
  have hlogm : Real.log (m : ℝ) ≤ Real.log (6 * s) :=
    Real.log_le_log hm0 (by linarith only [hm, hs])
  have hlogden0 : 0 ≤ Real.log (2 * ((m : ℝ) + 1)) := Real.log_nonneg (by linarith only [hmR])
  have hlogden : Real.log (2 * ((m : ℝ) + 1)) ≤ Real.log (6 * s) :=
    Real.log_le_log (by positivity) (by linarith only [hm, hs])
  have hprod : (2 * (m : ℝ)) * Real.log (2 * ((m : ℝ) + 1)) ≤
      4 * s * Real.log (6 * s) := by
    have hh := mul_le_mul (show 2 * (m : ℝ) ≤ 4 * s by linarith only [hm]) hlogden
      hlogden0 (by positivity : 0 ≤ 4 * s)
    exact hh
  have hlog8 : Real.log 8 ≤ (3 : ℝ) := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9]
  have hlog : Real.log (compactHatLower m) = -Real.log 8 -
      2 * (m : ℝ) * Real.log (2 * ((m : ℝ) + 1)) - 2 * Real.log (m : ℝ) := by
    unfold compactHatLower
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_div (by norm_num) (by norm_num), Real.log_one,
      Real.log_div (by norm_num) (by positivity), Real.log_one]
    push_cast
    ring
  have hexp : -8 * s * Real.log (6 * s) ≤ Real.log (compactHatLower m) := by
    rw [hlog]
    have hh := mul_le_mul_of_nonneg_left hA1 (show 0 ≤ 4 * s - 2 by linarith only [hs])
    nlinarith only [hprod, hlogm, hlog8, hh, hs]
  calc
    _ ≤ Real.exp (Real.log (compactHatLower m)) := Real.exp_le_exp.mpr hexp
    _ = compactHatLower m := Real.exp_log (compactHatLower_pos hm3)
    _ ≤ _ := numerical_hat_compact hH hm3 sign hs hsm

#print axioms numerical_hat_lower_profile
end ChenEffective
