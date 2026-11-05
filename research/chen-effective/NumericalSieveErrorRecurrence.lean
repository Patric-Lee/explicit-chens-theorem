import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
An explicit scalar majorant for the specialized linear-sieve error recurrence.
The indices start at zero: even indices represent the paper's odd layers.
This file proves the numerical summation step, not the sieve induction.
-/

namespace ChenEffective
open Finset

noncomputable def coarseSieveError : ℕ → ℝ
  | 0 => 3
  | n + 1 => (973 / 1000 : ℝ) * coarseSieveError n + 12 * (961 / 1000 : ℝ) ^ n

theorem coarseSieveError_nonneg (n : ℕ) : 0 ≤ coarseSieveError n := by
  induction n with
  | zero => norm_num [coarseSieveError]
  | succ n ih => simp only [coarseSieveError]; positivity

private noncomputable def evenPotential (x : ℝ) (n : ℕ) : ℝ :=
  (x + 12 * ((973 / 1000 : ℝ) + 961 / 1000) *
    (961 / 1000 : ℝ) ^ n / (1 - (961 / 1000 : ℝ) ^ 2)) /
    (1 - (973 / 1000 : ℝ) ^ 2)

private theorem evenPotential_step (n : ℕ) :
    evenPotential (coarseSieveError n) n = coarseSieveError n +
      evenPotential (coarseSieveError (n + 2)) (n + 2) := by
  simp only [evenPotential, coarseSieveError, pow_succ]
  ring

theorem coarseSieveError_even_partial (m : ℕ) :
    (∑ j ∈ range m, coarseSieveError (2 * j)) +
      evenPotential (coarseSieveError (2 * m)) (2 * m) =
        evenPotential (coarseSieveError 0) 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have h := evenPotential_step (2 * m)
    rw [show 2 * (m + 1) = 2 * m + 2 by omega]
    linarith

theorem coarseSieveError_even_sum_le (m : ℕ) :
    (∑ j ∈ range m, coarseSieveError (2 * j)) ≤ 6000 := by
  have h := coarseSieveError_even_partial m
  have hp : 0 ≤ evenPotential (coarseSieveError (2 * m)) (2 * m) := by
    have hx := coarseSieveError_nonneg (2 * m)
    unfold evenPotential
    positivity
  have h0 : evenPotential (coarseSieveError 0) 0 ≤ 6000 := by
    norm_num [evenPotential, coarseSieveError]
  linarith

theorem coarseSieveError_odd_partial (m : ℕ) :
    (∑ j ∈ range m, coarseSieveError (2 * j + 1)) +
      evenPotential (coarseSieveError (2 * m + 1)) (2 * m + 1) =
        evenPotential (coarseSieveError 1) 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have h := evenPotential_step (2 * m + 1)
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega]
    linarith

theorem coarseSieveError_odd_sum_le (m : ℕ) :
    (∑ j ∈ range m, coarseSieveError (2 * j + 1)) ≤ 6000 := by
  have h := coarseSieveError_odd_partial m
  have hp : 0 ≤ evenPotential (coarseSieveError (2 * m + 1)) (2 * m + 1) := by
    have hx := coarseSieveError_nonneg (2 * m + 1)
    unfold evenPotential
    positivity
  have h0 : evenPotential (coarseSieveError 1) 1 ≤ 6000 := by
    norm_num [evenPotential, coarseSieveError]
  linarith

/-- Every nonnegative error sequence with these numerical recurrence bounds
has both parity sums bounded uniformly in the depth. -/
theorem sieve_error_recurrence_majorant {t : ℕ → ℝ}
    (hzero : t 0 ≤ 3)
    (hstep : ∀ n, t (n + 1) ≤ (973 / 1000 : ℝ) * t n +
      12 * (961 / 1000 : ℝ) ^ n) :
    ∀ n, t n ≤ coarseSieveError n := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    exact (hstep n).trans (by
      simp only [coarseSieveError]
      gcongr)

theorem sieve_error_recurrence_parity_sums {t : ℕ → ℝ}
    (hzero : t 0 ≤ 3)
    (hstep : ∀ n, t (n + 1) ≤ (973 / 1000 : ℝ) * t n +
      12 * (961 / 1000 : ℝ) ^ n) (m : ℕ) :
    (∑ j ∈ range m, t (2 * j)) ≤ 6000 ∧
    (∑ j ∈ range m, t (2 * j + 1)) ≤ 6000 := by
  have h := sieve_error_recurrence_majorant hzero hstep
  constructor
  · exact (sum_le_sum (fun _ _ => h _)).trans (coarseSieveError_even_sum_le m)
  · exact (sum_le_sum (fun _ _ => h _)).trans (coarseSieveError_odd_sum_le m)

#print axioms sieve_error_recurrence_parity_sums

theorem specialized_sieve_error_step {ε t : ℝ} (hε : 0 ≤ ε)
    (hεcap : ε ≤ 1 / 200) (ht : 0 ≤ t) (n : ℕ) :
    ((9607 / 10000 : ℝ) + (Real.exp (1 / 5) + 9607 / 10000) * ε) * t +
      (8 * Real.exp 1 / 3 + 2 * (2 + ε) * (9607 / 10000)) *
        (9607 / 10000 : ℝ) ^ n ≤
      (973 / 1000 : ℝ) * t + 12 * (961 / 1000 : ℝ) ^ n := by
  have hg : Real.exp (1 / 5 : ℝ) ≤ 5 / 4 := by
    convert Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 1 / 5) (by norm_num : (1 / 5 : ℝ) < 1) using 1; norm_num
  have ha : (9607 / 10000 : ℝ) + (Real.exp (1 / 5) + 9607 / 10000) * ε ≤
      973 / 1000 := by
    have hh := mul_le_mul_of_nonneg_right (by linarith only [hg] :
      Real.exp (1 / 5) + (9607 / 10000 : ℝ) ≤ 5 / 4 + 9607 / 10000) hε
    linarith
  have hb : 8 * Real.exp 1 / 3 + 2 * (2 + ε) * (9607 / 10000 : ℝ) ≤ 12 := by
    linarith [Real.exp_one_lt_three]
  have hp : (9607 / 10000 : ℝ) ^ n ≤ (961 / 1000 : ℝ) ^ n := by
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
  exact add_le_add (mul_le_mul_of_nonneg_right ha ht)
    ((mul_le_mul_of_nonneg_right hb (by positivity)).trans
      (mul_le_mul_of_nonneg_left hp (by norm_num)))

/-- The analytic coarse recurrence, with the constants occurring in the
specialized sieve, has summable parity errors bounded by 6000. Establishing
this recurrence for actual sieve layers is a separate analytic obligation. -/
theorem specialized_sieve_error_sums {ε : ℝ} (hε : 0 ≤ ε) (hεcap : ε ≤ 1 / 200)
    {t : ℕ → ℝ} (ht : ∀ n, 0 ≤ t n) (hzero : t 0 ≤ 3)
    (hstep : ∀ n, t (n + 1) ≤
      ((9607 / 10000 : ℝ) + (Real.exp (1 / 5) + 9607 / 10000) * ε) * t n +
      (8 * Real.exp 1 / 3 + 2 * (2 + ε) * (9607 / 10000)) *
        (9607 / 10000 : ℝ) ^ n) :
    Summable (fun j => t (2 * j)) ∧ Summable (fun j => t (2 * j + 1)) ∧
      (∑' j, t (2 * j)) ≤ 6000 ∧ (∑' j, t (2 * j + 1)) ≤ 6000 := by
  have hs : ∀ n, t (n + 1) ≤ (973 / 1000 : ℝ) * t n +
      12 * (961 / 1000 : ℝ) ^ n := fun n =>
    (hstep n).trans (specialized_sieve_error_step hε hεcap (ht n) n)
  have hp := sieve_error_recurrence_parity_sums hzero hs
  exact ⟨summable_of_sum_range_le (fun _ => ht _) (fun m => (hp m).1),
    summable_of_sum_range_le (fun _ => ht _) (fun m => (hp m).2),
    Real.tsum_le_of_sum_range_le (fun _ => ht _) (fun m => (hp m).1),
    Real.tsum_le_of_sum_range_le (fun _ => ht _) (fun m => (hp m).2)⟩

#print axioms specialized_sieve_error_sums

noncomputable def specializedSieveError (ε : ℝ) : ℕ → ℝ
  | 0 => 3
  | n + 1 =>
    ((9607 / 10000 : ℝ) + (Real.exp (1 / 5) + 9607 / 10000) * ε) *
      specializedSieveError ε n +
    (8 * Real.exp 1 / 3 + 2 * (2 + ε) * (9607 / 10000)) *
      (9607 / 10000 : ℝ) ^ n

theorem specializedSieveError_nonneg {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    0 ≤ specializedSieveError ε n := by
  induction n with
  | zero => norm_num [specializedSieveError]
  | succ n ih => simp only [specializedSieveError]; positivity

theorem specializedSieveError_certified {ε : ℝ} (hε : 0 ≤ ε) (hεcap : ε ≤ 1 / 200) :
    Summable (fun j => specializedSieveError ε (2 * j)) ∧
      Summable (fun j => specializedSieveError ε (2 * j + 1)) ∧
      (∑' j, specializedSieveError ε (2 * j)) ≤ 6000 ∧
      (∑' j, specializedSieveError ε (2 * j + 1)) ≤ 6000 := by
  apply specialized_sieve_error_sums hε hεcap (specializedSieveError_nonneg hε)
  · exact le_rfl
  · intro n; exact le_rfl

#print axioms specializedSieveError_certified
end ChenEffective
