import NumericalElementaryMertens
import AnalyticNumberTheory.Mertens.Basic

namespace ChenEffective
open Real AnalyticNumberTheory.Mertens
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

@[irreducible] def globalMertensBudget : ℕ := 10

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

/-- The finite prime sum uses the elementary Mertens constant. Its value cancels
in the interval-product application; no PNT cutoff or chosen threshold is used. -/
theorem numerical_mertens_all {n : ℕ} (hn : 2 ≤ n) :
    |primeReciprocalSum n - (Real.log (Real.log (n : ℝ)) + ElementaryMertens.M)| ≤
      (globalMertensBudget : ℝ) / Real.log (n : ℝ) := by
  have h := ElementaryMertens.prime_reciprocal_error_ten
    (show (2 : ℝ) ≤ n by exact_mod_cast hn)
  have hsum : (∑ p ∈ Finset.Ioc 0 n with p.Prime, (1 : ℝ)/p) = primeReciprocalSum n := by
    unfold primeReciprocalSum primesUpTo
    have hs : (Finset.Ioc 0 n).filter Nat.Prime = (Finset.range (n+1)).filter Nat.Prime := by
      ext p
      simp only [Finset.mem_filter,Finset.mem_Ioc,Finset.mem_range]
      constructor
      · intro hp
        exact ⟨by omega,hp.2⟩
      · intro hp
        exact ⟨⟨hp.2.pos,by omega⟩,hp.2⟩
    rw [hs]
  rw [Nat.floor_natCast,hsum] at h
  simpa only [globalMertensBudget,Nat.cast_ofNat,sub_add_eq_sub_sub] using h

#print axioms numerical_mertens_all
end ChenEffective
