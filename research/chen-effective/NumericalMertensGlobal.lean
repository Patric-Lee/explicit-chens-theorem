import NumericalMertens

namespace ChenEffective
open Real AnalyticNumberTheory.Mertens
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

@[irreducible] def globalMertensBudget : ℕ :=
  (4 * principalNumericalThreshold 1 + 900000000006) * principalNumericalThreshold 1

theorem numerical_reciprocal_prefix (n : ℕ) :
    0 ≤ primeReciprocalSum n ∧ primeReciprocalSum n ≤ (n : ℝ) + 1 := by
  unfold primeReciprocalSum
  refine ⟨Finset.sum_nonneg (fun p _ => by positivity), ?_⟩
  calc
    _ ≤ ∑ _p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp2 := (Finset.mem_filter.mp hp).2.two_le
      exact div_le_self (by norm_num) (by exact_mod_cast (show 1 ≤ p by omega))
    _ = (((Finset.range (n + 1)).filter Nat.Prime).card : ℝ) := by simp
    _ ≤ (n : ℝ) + 1 := by
      have hh := Finset.card_filter_le (Finset.range (n + 1)) Nat.Prime
      rw [Finset.card_range] at hh
      exact_mod_cast hh

theorem numerical_log_log_nat {n : ℕ} (hn : 2 ≤ n) :
    |Real.log (Real.log (n : ℝ))| ≤ (n : ℝ) + 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : (1 / 2 : ℝ) ≤ Real.log (n : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn2
    linarith only [hh, Real.log_two_gt_d9]
  have hl0 : 0 < Real.log (n : ℝ) := by linarith only [hl]
  have hlow := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hl
  have hhalf : Real.log (1 / 2 : ℝ) = - Real.log 2 := by rw [one_div, Real.log_inv]
  rw [hhalf] at hlow
  have hhigh := Real.log_le_sub_one_of_pos hl0
  have hln := Real.log_le_sub_one_of_pos hn0
  rw [abs_le]
  constructor <;> linarith only [hlow, hhigh, hln, Real.log_two_lt_d9, hn2]

/-- A numerical constant valid at every integer endpoint, including below the PNT cutoff. -/
theorem numerical_mertens_all {n : ℕ} (hn : 2 ≤ n) :
    |primeReciprocalSum n - (Real.log (Real.log (n : ℝ)) + mertensSecondConstant)| ≤
      (globalMertensBudget : ℝ) / Real.log (n : ℝ) := by
  let n0 := principalNumericalThreshold 1
  have hn09 : 9 ≤ n0 := logPowerCutoff_nine_le _
  have hn0R : (9 : ℝ) ≤ n0 := by exact_mod_cast hn09
  have hn0pos : (0 : ℝ) < n0 := by linarith only [hn0R]
  have hlog0 : 1 ≤ Real.log (n0 : ℝ) := numerical_mertens_log_one (le_refl _)
  have hC : (globalMertensBudget : ℝ) = (4 * (n0 : ℝ) + 900000000006) * n0 := by
    unfold globalMertensBudget
    change (((4 * n0 + 900000000006) * n0 : ℕ) : ℝ) = _
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_mul]
    norm_num only [Nat.cast_ofNat]
  have hCQ : (900000000000 : ℝ) ≤ globalMertensBudget := by
    rw [hC]
    nlinarith only [hn0R, sq_nonneg (n0 : ℝ)]
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  by_cases hlarge : n0 ≤ n
  · have hh := numerical_mertens_second (show (principalNumericalThreshold 1 : ℝ) ≤ n by exact_mod_cast hlarge)
    rw [Nat.floor_natCast] at hh
    exact hh.trans (div_le_div_of_nonneg_right hCQ hl.le)
  · have hnle : n ≤ n0 := by omega
    have hnleR : (n : ℝ) ≤ n0 := by exact_mod_cast hnle
    have hb0 := numerical_mertens_second (x := (n0 : ℝ)) (le_refl _)
    rw [Nat.floor_natCast] at hb0
    have hb0' : |primeReciprocalSum n0 -
        (Real.log (Real.log (n0 : ℝ)) + mertensSecondConstant)| ≤ 900000000000 :=
      hb0.trans (div_le_self (by norm_num) hlog0)
    have hp0 := numerical_reciprocal_prefix n0
    have hll0 := numerical_log_log_nat (show 2 ≤ n0 by omega)
    have hB : |mertensSecondConstant| ≤ 2 * (n0 : ℝ) + 900000000003 := by
      rw [abs_le] at hb0' hll0 ⊢
      constructor <;> linarith only [hb0'.1, hb0'.2, hp0.1, hp0.2, hll0.1, hll0.2]
    have hp := numerical_reciprocal_prefix n
    have hll := numerical_log_log_nat hn
    have herr : |primeReciprocalSum n -
        (Real.log (Real.log (n : ℝ)) + mertensSecondConstant)| ≤
        4 * (n0 : ℝ) + 900000000006 := by
      rw [abs_le] at hB hll ⊢
      constructor <;> linarith only [hB.1, hB.2, hll.1, hll.2, hp.1, hp.2, hnleR]
    apply herr.trans
    apply (le_div_iff₀ hl).mpr
    rw [hC]
    have hln : Real.log (n : ℝ) ≤ n0 :=
      (Real.log_le_sub_one_of_pos (by exact_mod_cast (show 0 < n by omega))).trans
        (by linarith only [hnleR])
    exact mul_le_mul_of_nonneg_left hln (by linarith only [hn0pos])

#print axioms numerical_mertens_all
end ChenEffective
