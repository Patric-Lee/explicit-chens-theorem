import ExplicitLogBounds

namespace ChenEffective
set_option maxHeartbeats 800000

theorem real_log_ge_power_three {b : ℕ} {x : ℝ} (hx : ((3 ^ b : ℕ) : ℝ) ≤ x) :
    (b : ℝ) ≤ Real.log x := by
  have hp : (0 : ℝ) < (3 ^ b : ℕ) := by exact_mod_cast (pow_pos (by norm_num : (0 : ℕ) < 3) b)
  exact (log_ge_power_three (b := b) (N := 3 ^ b) (le_refl _)).trans (Real.log_le_log hp hx)

theorem real_log_power_cutoff_log {k : ℕ} {x : ℝ}
    (hx : (logPowerCutoff k : ℝ) ≤ x) :
    16 * ((k : ℝ) + 1) ^ 2 ≤ Real.log x := by
  have hp : (0 : ℝ) < (logPowerCutoff k : ℕ) := by
    exact_mod_cast (show 0 < logPowerCutoff k by unfold logPowerCutoff; positivity)
  exact (log_power_cutoff_log (N := logPowerCutoff k) (le_refl _)).trans
    (Real.log_le_log hp hx)

theorem real_log_power_cutoff_nine {k : ℕ} {x : ℝ}
    (hx : (logPowerCutoff k : ℝ) ≤ x) : 9 ≤ x :=
  (show (9 : ℝ) ≤ (logPowerCutoff k : ℕ) by exact_mod_cast logPowerCutoff_nine_le k).trans hx

/-- The numerical logarithmic payment at real endpoints, including x=log(D). -/
theorem real_log_pow_le_sqrt {k : ℕ} {x : ℝ} (hx : (logPowerCutoff k : ℝ) ≤ x) :
    Real.log x ^ k ≤ Real.sqrt x := by
  have hx9 := real_log_power_cutoff_nine hx
  have hx0 : 0 < x := by linarith only [hx9]
  let L := Real.log x
  have hL := real_log_power_cutoff_log hx
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hL0 : 0 < L := by dsimp [L]; nlinarith only [hL, hk, sq_nonneg (k : ℝ)]
  have hs : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hs2 : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
  have hs4 : 4 * (k : ℝ) ≤ Real.sqrt L := by
    change 16 * ((k : ℝ) + 1) ^ 2 ≤ L at hL
    nlinarith only [hL, hs, hk, hs2, sq_nonneg (Real.sqrt L - 4 * (k : ℝ))]
  have hlog : Real.log L ≤ 2 * Real.sqrt L := by
    have h := Real.log_le_rpow_div hL0.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    linarith only [h]
  have hpay : (k : ℝ) * Real.log L ≤ L / 2 := by
    have hm := mul_le_mul_of_nonneg_left hlog hk
    have hm' := mul_le_mul_of_nonneg_right hs4 hs
    nlinarith only [hm, hm', hs2]
  apply (Real.log_le_log_iff (pow_pos hL0 k) (Real.sqrt_pos.mpr hx0)).mp
  rw [Real.log_pow, Real.log_sqrt hx0.le]
  exact hpay

theorem real_log_pow_le_rpow_inv {k m t : ℕ} {x : ℝ} (hm : 0 < m)
    (hmt : m * k ≤ t) (hx : (logPowerCutoff t : ℝ) ≤ x) :
    Real.log x ^ k ≤ x ^ (1 / (m : ℝ)) := by
  have hx9 := real_log_power_cutoff_nine hx
  have hx1 : 1 ≤ x := by linarith only [hx9]
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlarge := real_log_power_cutoff_log hx
  have hl1 : 1 ≤ Real.log x := by
    nlinarith only [hlarge, show (0 : ℝ) ≤ t from Nat.cast_nonneg t, sq_nonneg (t : ℝ)]
  have hg := (pow_le_pow_right₀ hl1 hmt).trans (real_log_pow_le_sqrt hx)
  have hp : (Real.log x ^ k) ^ (m : ℝ) ≤ x := by
    rw [Real.rpow_natCast, ← pow_mul, Nat.mul_comm k m]
    exact hg.trans (Real.sqrt_le_self_iff.mpr (Or.inr hx1))
  simpa only [one_div] using
    (Real.le_rpow_inv_iff_of_pos (pow_nonneg hl k) (by linarith only [hx9] : 0 ≤ x)
      (show (0 : ℝ) < m by exact_mod_cast hm)).mpr hp

#print axioms real_log_pow_le_rpow_inv
end ChenEffective
