import MathlibNt.AnalyticNumberTheory.LargeSieve.LogPowerBounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Numerical replacements for logarithmic-versus-power eventual bounds.
No new axioms. Deliberately generous integer thresholds. -/
namespace ChenEffective
set_option maxHeartbeats 400000

def logPowerCutoff (k : ℕ) : ℕ := 3 ^ (16 * (k + 1) ^ 2)

theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 8) (by norm_num : (8 : ℝ) ≤ 9)
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, show (9 : ℝ) = 3 ^ 2 by norm_num,
    Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith [Real.log_two_gt_d9]

theorem log_ge_power_three {b N : ℕ} (hN : 3 ^ b ≤ N) :
    (b : ℝ) ≤ Real.log (N : ℝ) := by
  have hp : (0 : ℝ) < (3 ^ b : ℕ) := by exact_mod_cast (pow_pos (by norm_num : 0 < (3 : ℕ)) b)
  have h := Real.log_le_log hp (show ((3 ^ b : ℕ) : ℝ) ≤ N by exact_mod_cast hN)
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h
  nlinarith only [h, one_le_log_three, show (0 : ℝ) ≤ b from Nat.cast_nonneg b]

theorem log_power_cutoff_log {k N : ℕ} (hN : logPowerCutoff k ≤ N) :
    16 * ((k : ℝ) + 1) ^ 2 ≤ Real.log (N : ℝ) := by
  have hp : (0 : ℝ) < (logPowerCutoff k : ℕ) := by
    exact_mod_cast (show 0 < logPowerCutoff k by unfold logPowerCutoff; positivity)
  have h := Real.log_le_log hp
    (show (logPowerCutoff k : ℝ) ≤ (N : ℝ) by exact_mod_cast hN)
  have heq : Real.log (logPowerCutoff k : ℝ) =
      (16 * ((k : ℝ) + 1) ^ 2) * Real.log 3 := by
    rw [show (logPowerCutoff k : ℝ) = (3 : ℝ) ^ (16 * (k + 1) ^ 2) by
      simp only [logPowerCutoff, Nat.cast_pow, Nat.cast_ofNat]]
    rw [Real.log_pow]
    push_cast
    ring
  rw [heq] at h
  nlinarith only [h, one_le_log_three, sq_nonneg ((k : ℝ) + 1)]

theorem logPowerCutoff_nine_le (k : ℕ) : 9 ≤ logPowerCutoff k := by
  have he : 2 ≤ 16 * (k + 1) ^ 2 := by nlinarith [Nat.zero_le k, Nat.zero_le (k * k)]
  exact (show (9 : ℕ) = 3 ^ 2 by norm_num).le.trans
    (Nat.pow_le_pow_right (by norm_num) he)

/-- Unlike the existing asymptotic lemma, this supplies an actual integer
starting point for every exponent. -/
theorem log_pow_le_sqrt_explicit {k N : ℕ} (hN : logPowerCutoff k ≤ N) :
    Real.log (N : ℝ) ^ k ≤ Real.sqrt N := by
  have hN9 : 9 ≤ N := (logPowerCutoff_nine_le k).trans hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let L := Real.log (N : ℝ)
  have hL := log_power_cutoff_log hN
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hL0 : 0 < L := by dsimp [L]; nlinarith only [hL, hk, sq_nonneg (k : ℝ)]
  have hs : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hs2 : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
  have hs4 : 4 * (k : ℝ) ≤ Real.sqrt L := by
    dsimp [L] at hs2
    change 16 * ((k : ℝ) + 1) ^ 2 ≤ L at hL
    nlinarith only [hL, hs, hk, hs2, sq_nonneg (Real.sqrt L - 4 * (k : ℝ))]
  have hlog : Real.log L ≤ 2 * Real.sqrt L := by
    have h := Real.log_le_rpow_div hL0.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    linarith
  have hpay : (k : ℝ) * Real.log L ≤ L / 2 := by
    have hm := mul_le_mul_of_nonneg_left hlog hk
    have hm' := mul_le_mul_of_nonneg_right hs4 hs
    nlinarith only [hm, hm', hs2]
  apply (Real.log_le_log_iff (pow_pos hL0 k) (Real.sqrt_pos.mpr hN0)).mp
  rw [Real.log_pow, Real.log_sqrt hN0.le]
  exact hpay

theorem log_pow_le_sqrt_explicit_of_le {k m N : ℕ} (hkm : k ≤ m)
    (hN : logPowerCutoff m ≤ N) : Real.log (N : ℝ) ^ k ≤ Real.sqrt N := by
  have hlarge := log_power_cutoff_log hN
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    nlinarith only [hlarge, show (0 : ℝ) ≤ m from Nat.cast_nonneg m, sq_nonneg (m : ℝ)]
  exact (pow_le_pow_right₀ hlog hkm).trans (log_pow_le_sqrt_explicit hN)

/-- Rational power savings with the same integer cutoff mechanism. -/
theorem log_pow_le_rpow_inv_explicit {k m t N : ℕ} (hm : 0 < m)
    (hmt : m * k ≤ t) (hN : logPowerCutoff t ≤ N) :
    Real.log (N : ℝ) ^ k ≤ (N : ℝ) ^ (1 / (m : ℝ)) := by
  have hg := log_pow_le_sqrt_explicit_of_le hmt hN
  have hN9 : 9 ≤ N := (logPowerCutoff_nine_le _).trans hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hp : (Real.log (N : ℝ) ^ k) ^ (m : ℝ) ≤ (N : ℝ) := by
    rw [Real.rpow_natCast, ← pow_mul, Nat.mul_comm k m]
    exact hg.trans (Real.sqrt_le_self_iff.mpr (Or.inr hN1))
  simpa only [one_div] using
    (Real.le_rpow_inv_iff_of_pos (pow_nonneg hl k) (Nat.cast_nonneg N)
      (show (0 : ℝ) < m by exact_mod_cast hm)).mpr hp

theorem power_saving_payment_explicit {k m t N : ℕ} (hm : 0 < m)
    (hmt : m * k ≤ t) (hN : logPowerCutoff t ≤ N)
    (C : ℝ) (hC : 0 ≤ C) :
    C * (N : ℝ) ^ (1 - 1 / (m : ℝ)) ≤ C * N / Real.log N ^ k := by
  have hN9 : 9 ≤ N := (logPowerCutoff_nine_le _).trans hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hg := log_pow_le_rpow_inv_explicit hm hmt hN
  have hcombine : (N : ℝ) ^ (1 - 1 / (m : ℝ)) * Real.log N ^ k ≤ N := by
    calc
      _ ≤ (N : ℝ) ^ (1 - 1 / (m : ℝ)) * (N : ℝ) ^ (1 / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg hN0.le _)
      _ = N := by rw [← Real.rpow_add hN0, sub_add_cancel, Real.rpow_one]
  apply (le_div_iff₀ (pow_pos hl k)).mpr
  calc
    _ = C * ((N : ℝ) ^ (1 - 1 / (m : ℝ)) * Real.log N ^ k) := by ring
    _ ≤ C * N := mul_le_mul_of_nonneg_left hcombine hC

#print axioms log_pow_le_sqrt_explicit
end ChenEffective
