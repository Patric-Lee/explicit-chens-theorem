import NumericalSuzukiGate

namespace ChenEffective
open Real
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def suzukiScalarThreshold (M r : ℕ) : ℕ :=
  3 ^ (max 152587890625 (4096 * (M + 1) ^ 2 * r ^ 2))

/-- A numerical replacement for the scalar limit in the Suzuki absorption.
The remaining sieve task is to bound its actual amplitude by the integer M. -/
theorem numerical_suzuki_scalar_absorption {D M r : ℕ} {s a : ℝ}
    (hD : suzukiScalarThreshold M r ≤ D) (hr : 0 < r)
    (hs : 0 < s) (hs5 : s ≤ 5) (_ha : 0 ≤ a) (haM : a ≤ M) :
    a * (1 + s ^ (16 : ℕ) / Real.log D) ^ s *
      (Real.log D) ^ (-(1 / 2 : ℝ)) < 1 / (r : ℝ) := by
  have hlog := log_ge_power_three
    (b := max 152587890625 (4096 * (M + 1) ^ 2 * r ^ 2)) hD
  have hL5 : (5 : ℝ) ^ (16 : ℕ) ≤ Real.log D := by
    have hh := (show (152587890625 : ℕ) ≤ max 152587890625 (4096 * (M + 1) ^ 2 * r ^ 2)
      from le_max_left _ _)
    have hhR : (152587890625 : ℝ) ≤
        (max 152587890625 (4096 * (M + 1) ^ 2 * r ^ 2) : ℕ) := by exact_mod_cast hh
    have hn := hhR.trans hlog
    norm_num only [Nat.reducePow] at hn ⊢
    exact hn
  have hL : 0 < Real.log (D : ℝ) := lt_of_lt_of_le (by norm_num) hL5
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hscale : 4096 * ((M : ℝ) + 1) ^ 2 * (r : ℝ) ^ 2 ≤ Real.log D := by
    calc
      _ = ((4096 * (M + 1) ^ 2 * r ^ 2 : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ (max 152587890625 (4096 * (M + 1) ^ 2 * r ^ 2) : ℕ) := by
        exact_mod_cast (le_max_right 152587890625 (4096 * (M + 1) ^ 2 * r ^ 2))
      _ ≤ _ := hlog
  have hroot : 64 * ((M : ℝ) + 1) * r ≤ Real.sqrt (Real.log D) := by
    apply (Real.le_sqrt (by positivity) hL.le).mpr
    nlinarith only [hscale]
  have hratio : s ^ (16 : ℕ) / Real.log D ≤ 1 :=
    (div_le_one hL).mpr ((pow_le_pow_left₀ hs.le hs5 16).trans hL5)
  have hperturb : (1 + s ^ (16 : ℕ) / Real.log D) ^ s ≤ 32 := by
    calc
      _ ≤ (2 : ℝ) ^ s := Real.rpow_le_rpow (by positivity) (by linarith only [hratio]) hs.le
      _ ≤ (2 : ℝ) ^ (5 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs5
      _ = _ := by norm_num
  have he : (Real.log (D : ℝ)) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (Real.log D))⁻¹ := by
    rw [Real.rpow_neg hL.le, Real.sqrt_eq_rpow]
  rw [he]
  have hroot0 : 0 < Real.sqrt (Real.log D) := Real.sqrt_pos.mpr hL
  calc
    _ ≤ (M : ℝ) * 32 * (Real.sqrt (Real.log D))⁻¹ := by gcongr
    _ ≤ 1 / (2 * (r : ℝ)) := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ hroot0 (by positivity)]
      nlinarith only [hroot, hrR]
    _ < 1 / (r : ℝ) := one_div_lt_one_div_of_lt hrR (by linarith only [hrR])

#print axioms numerical_suzuki_scalar_absorption
end ChenEffective
