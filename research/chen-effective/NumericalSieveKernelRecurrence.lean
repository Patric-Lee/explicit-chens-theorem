import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
A scalar majorant matched to the proved analytic kernel constant 241/250.
The indices start at zero: even indices represent the paper's odd layers.
This file proves the numerical summation step, not the sieve induction.
-/

set_option backward.isDefEq.respectTransparency false
namespace ChenEffective
open Finset

noncomputable def kernelSieveError : ℕ → ℝ
  | 0 => 3
  | n + 1 => (965 / 1000 : ℝ) * kernelSieveError n + 12 * (964 / 1000 : ℝ) ^ n

theorem kernelSieveError_nonneg (n : ℕ) : 0 ≤ kernelSieveError n := by
  induction n with
  | zero => norm_num [kernelSieveError]
  | succ n ih => simp only [kernelSieveError]; positivity

private noncomputable def kernelEvenPotential (x : ℝ) (n : ℕ) : ℝ :=
  (x + 12 * ((965 / 1000 : ℝ) + 964 / 1000) *
    (964 / 1000 : ℝ) ^ n / (1 - (964 / 1000 : ℝ) ^ 2)) /
    (1 - (965 / 1000 : ℝ) ^ 2)

private theorem kernelEvenPotential_step (n : ℕ) :
    kernelEvenPotential (kernelSieveError n) n = kernelSieveError n +
      kernelEvenPotential (kernelSieveError (n + 2)) (n + 2) := by
  simp only [kernelEvenPotential, kernelSieveError, pow_succ]
  ring

theorem kernelSieveError_even_partial (m : ℕ) :
    (∑ j ∈ range m, kernelSieveError (2 * j)) +
      kernelEvenPotential (kernelSieveError (2 * m)) (2 * m) =
        kernelEvenPotential (kernelSieveError 0) 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have h := kernelEvenPotential_step (2 * m)
    rw [show 2 * (m + 1) = 2 * m + 2 by omega]
    linarith

theorem kernelSieveError_even_sum_le (m : ℕ) :
    (∑ j ∈ range m, kernelSieveError (2 * j)) ≤ 6000 := by
  have h := kernelSieveError_even_partial m
  have hp : 0 ≤ kernelEvenPotential (kernelSieveError (2 * m)) (2 * m) := by
    have hx := kernelSieveError_nonneg (2 * m)
    unfold kernelEvenPotential
    positivity
  have h0 : kernelEvenPotential (kernelSieveError 0) 0 ≤ 6000 := by
    norm_num [kernelEvenPotential, kernelSieveError]
  linarith

theorem kernelSieveError_odd_partial (m : ℕ) :
    (∑ j ∈ range m, kernelSieveError (2 * j + 1)) +
      kernelEvenPotential (kernelSieveError (2 * m + 1)) (2 * m + 1) =
        kernelEvenPotential (kernelSieveError 1) 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have h := kernelEvenPotential_step (2 * m + 1)
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega]
    linarith

theorem kernelSieveError_odd_sum_le (m : ℕ) :
    (∑ j ∈ range m, kernelSieveError (2 * j + 1)) ≤ 6000 := by
  have h := kernelSieveError_odd_partial m
  have hp : 0 ≤ kernelEvenPotential (kernelSieveError (2 * m + 1)) (2 * m + 1) := by
    have hx := kernelSieveError_nonneg (2 * m + 1)
    unfold kernelEvenPotential
    positivity
  have h0 : kernelEvenPotential (kernelSieveError 1) 1 ≤ 6000 := by
    norm_num [kernelEvenPotential, kernelSieveError]
  linarith

/-- Every nonnegative error sequence with these numerical recurrence bounds
has both parity sums bounded uniformly in the depth. -/
theorem kernel_sieve_error_recurrence_majorant {t : ℕ → ℝ}
    (hzero : t 0 ≤ 3)
    (hstep : ∀ n, t (n + 1) ≤ (965 / 1000 : ℝ) * t n +
      12 * (964 / 1000 : ℝ) ^ n) :
    ∀ n, t n ≤ kernelSieveError n := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    exact (hstep n).trans (by
      simp only [kernelSieveError]
      gcongr)

theorem kernel_sieve_error_recurrence_parity_sums {t : ℕ → ℝ}
    (hzero : t 0 ≤ 3)
    (hstep : ∀ n, t (n + 1) ≤ (965 / 1000 : ℝ) * t n +
      12 * (964 / 1000 : ℝ) ^ n) (m : ℕ) :
    (∑ j ∈ range m, t (2 * j)) ≤ 6000 ∧
    (∑ j ∈ range m, t (2 * j + 1)) ≤ 6000 := by
  have h := kernel_sieve_error_recurrence_majorant hzero hstep
  constructor
  · exact (sum_le_sum (fun _ _ => h _)).trans (kernelSieveError_even_sum_le m)
  · exact (sum_le_sum (fun _ _ => h _)).trans (kernelSieveError_odd_sum_le m)

#print axioms kernel_sieve_error_recurrence_parity_sums

theorem kernel_sieve_step_cap {ε t : ℝ} (hε : 0 ≤ ε)
    (hεcap : ε ≤ 1 / 10000) (ht : 0 ≤ t) (n : ℕ) :
    ((1 + ε) ^ 2 * (241 / 250 : ℝ) + (1 + ε) * ε * 4) * t +
      (8 * (1 + ε) + 2 * (2 + ε) * (241 / 250 : ℝ)) *
        (241 / 250 : ℝ) ^ n ≤
      (965 / 1000 : ℝ) * t + 12 * (964 / 1000 : ℝ) ^ n := by
  have ha : (1 + ε) ^ 2 * (241 / 250 : ℝ) + (1 + ε) * ε * 4 ≤ 965 / 1000 := by
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hεcap)]
  have hb : 8 * (1 + ε) + 2 * (2 + ε) * (241 / 250 : ℝ) ≤ 12 := by
    linarith
  have hh := add_le_add (mul_le_mul_of_nonneg_right ha ht)
    (mul_le_mul_of_nonneg_right hb (show 0 ≤ (241 / 250 : ℝ) ^ n by positivity))
  convert! hh using 1; norm_num

theorem kernelSieveError_sums :
    Summable (fun j => kernelSieveError (2 * j)) ∧
      Summable (fun j => kernelSieveError (2 * j + 1)) ∧
      (∑' j, kernelSieveError (2 * j)) ≤ 6000 ∧
      (∑' j, kernelSieveError (2 * j + 1)) ≤ 6000 := by
  exact ⟨summable_of_sum_range_le (fun _ => kernelSieveError_nonneg _) kernelSieveError_even_sum_le,
    summable_of_sum_range_le (fun _ => kernelSieveError_nonneg _) kernelSieveError_odd_sum_le,
    Real.tsum_le_of_sum_range_le (fun _ => kernelSieveError_nonneg _) kernelSieveError_even_sum_le,
    Real.tsum_le_of_sum_range_le (fun _ => kernelSieveError_nonneg _) kernelSieveError_odd_sum_le⟩

#print axioms kernelSieveError_sums
end ChenEffective

