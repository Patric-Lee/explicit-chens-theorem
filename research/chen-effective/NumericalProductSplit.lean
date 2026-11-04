import NumericalProductExponential
import Mathlib.Algebra.BigOperators.Intervals

namespace ChenEffective
open Real Finset
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem goldbach_factor_one {p : ℕ} (hp : 2 < p) :
    1 ≤ (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
  apply (one_le_inv₀ (goldbach_factor_positive hp)).mpr
  have : 0 ≤ 1 / ((p : ℝ) - 1) := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp
    exact div_nonneg zero_le_one (by linarith)
  linarith

theorem goldbach_integer_product (n : ℕ) :
    (∏ p ∈ Finset.Icc 3 (n + 2), (1 - 1 / ((p : ℝ) - 1))⁻¹) = (n : ℝ) + 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by omega, Finset.prod_Icc_succ_top (by omega), ih]
    push_cast
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [show (n : ℝ) + 2 + 1 - 1 = n + 2 by ring]
    have he : (1 : ℝ) - 1 / ((n : ℝ) + 2) = (n + 1) / (n + 2) := by
      field_simp
      ring
    rw [he, inv_div]
    field_simp
    ring

theorem goldbach_small_product (s : Finset ℕ)
    (hs : ∀ p ∈ s, 2 < p ∧ p < 1024) :
    (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤ 1024 := by
  have hsub : s ⊆ Finset.Icc 3 (1023 + 2) := by
    intro p hp
    have hh := hs p hp
    simp only [Finset.mem_Icc]
    omega
  have hh := Finset.prod_le_prod_of_subset_of_one_le hsub
    (fun p hp => inv_nonneg.mpr (goldbach_factor_positive (hs p hp).1).le)
    (fun p hp _ => goldbach_factor_one (by have hh := (Finset.mem_Icc.mp hp).1; omega))
  have ht := goldbach_integer_product 1023
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at ht
  exact hh.trans_eq ht

theorem goldbach_log1024 : (6 : ℝ) ≤ log 1024 ∧ log 1024 ≤ 10 := by
  rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  constructor <;> linarith only [Real.log_two_gt_d9, Real.log_two_lt_d9]

theorem goldbach_exponential_numerical (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) (z₁ z₂ : ℝ) (hz₁ : 2 ≤ z₁) (hz₁₂ : z₁ ≤ z₂)
    (hsinterval : ∀ p ∈ s, z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂) :
    (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
      log z₂ / log z₁ * exp (90 / log z₁) := by
  have hh := goldbach_interval_exponential (Nat.cast_nonneg globalMertensBudget)
    (goldbach_log_interval_of_mertens (Nat.cast_nonneg globalMertensBudget)
      (fun _ hn => numerical_mertens_all hn)) s hs z₁ z₂ hz₁ hz₁₂ hsinterval
  have hL : 0 < log z₁ := Real.log_pos (by linarith only [hz₁])
  have hD : 2 * (2 * (globalMertensBudget : ℝ) + 24) + 2 * log 2 ≤ 90 := by
    norm_num [globalMertensBudget]
    linarith only [Real.log_two_lt_d9]
  have hratio : 0 ≤ log z₂ / log z₁ := by
    apply div_nonneg (Real.log_nonneg (by linarith only [hz₁, hz₁₂])) hL.le
  exact hh.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (div_le_div_of_nonneg_right hD hL.le)) hratio)

theorem goldbach_exp_large {z : ℝ} (hz : 1024 ≤ z) : exp (90 / log z) ≤ (3 : ℝ) ^ 15 := by
  have hL : 6 ≤ log z := goldbach_log1024.1.trans (Real.log_le_log (by norm_num) hz)
  have hh : 90 / log z ≤ (15 : ℝ) := (div_le_iff₀ (by linarith only [hL])).mpr (by linarith only [hL])
  calc
    _ ≤ exp 15 := Real.exp_le_exp.mpr hh
    _ = (exp 1) ^ 15 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos 1).le
      (Real.exp_one_lt_d9.le.trans (by norm_num)) 15

theorem goldbach_small_linear {z : ℝ} (hz : 2 ≤ z) (hzhi : z ≤ 1024) :
    (1024 : ℝ) * 3 ^ 15 ≤ 1 + (10 : ℝ) ^ 12 / log z := by
  have hL : 0 < log z := Real.log_pos (by linarith only [hz])
  have hLhi : log z ≤ 10 := (Real.log_le_log (by linarith only [hz]) hzhi).trans goldbach_log1024.2
  rw [show (1 : ℝ) + 10 ^ 12 / log z = (log z + 10 ^ 12) / log z by field_simp]
  apply (le_div_iff₀ hL).mpr
  norm_num
  nlinarith only [hLhi, hL]

theorem numerical_goldbach_split_interval (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) (z₁ z₂ : ℝ) (hz₁ : 2 ≤ z₁) (hz₁₂ : z₁ ≤ z₂)
    (hsinterval : ∀ p ∈ s, z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂) :
    (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
      log z₂ / log z₁ * (1 + (10 : ℝ) ^ 12 / log z₁) := by
  classical
  have hL : 0 < log z₁ := Real.log_pos (by linarith only [hz₁])
  have hL₂ : 0 < log z₂ := Real.log_pos (by linarith only [hz₁, hz₁₂])
  have hratio : 1 ≤ log z₂ / log z₁ := (one_le_div hL).mpr (Real.log_le_log (by linarith only [hz₁]) hz₁₂)
  by_cases hlarge : 1024 ≤ z₁
  · have he := goldbach_exponential_numerical s hs z₁ z₂ hz₁ hz₁₂ hsinterval
    have ht := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-(90 / log z₁))) (Real.exp_pos (90 / log z₁)).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at ht
    have hb := mul_le_mul_of_nonneg_left (goldbach_exp_large hlarge) (by positivity : 0 ≤ (90 : ℝ) / log z₁)
    have hbound : exp (90 / log z₁) ≤ 1 + (10 : ℝ) ^ 12 / log z₁ := by
      have hc : (90 : ℝ) * 3 ^ 15 / log z₁ ≤ (10 : ℝ) ^ 12 / log z₁ :=
        div_le_div_of_nonneg_right (by norm_num) hL.le
      ring_nf at ht hb hc ⊢
      nlinarith only [ht, hb, hc]
    exact he.trans (mul_le_mul_of_nonneg_left hbound (by positivity))
  · have hzlo : z₁ ≤ 1024 := (lt_of_not_ge hlarge).le
    have hlinear := goldbach_small_linear hz₁ hzlo
    by_cases hsmall : z₂ ≤ 1024
    · have hp := goldbach_small_product s (fun p hp => ⟨(hs p hp).2, by
        have hh := (hsinterval p hp).2.trans_le hsmall
        exact_mod_cast hh⟩)
      have hbig : (1024 : ℝ) ≤ 1 + (10 : ℝ) ^ 12 / log z₁ :=
        (by norm_num : (1024 : ℝ) ≤ 1024 * 3 ^ 15).trans hlinear
      exact hp.trans (hbig.trans (le_mul_of_one_le_left (by positivity) hratio))
    · let lo := s.filter (fun p => p < 1024)
      let hi := s.filter (fun p => ¬ p < 1024)
      have hlo := goldbach_small_product lo (fun p hp => ⟨(hs p (Finset.mem_filter.mp hp).1).2, (Finset.mem_filter.mp hp).2⟩)
      have hhi := goldbach_exponential_numerical hi (fun p hp => hs p (Finset.mem_filter.mp hp).1)
        1024 z₂ (by norm_num) (le_of_not_ge hsmall) (by
          intro p hp
          refine ⟨?_, (hsinterval p (Finset.mem_filter.mp hp).1).2⟩
          exact_mod_cast (Nat.le_of_not_gt (Finset.mem_filter.mp hp).2))
      have hb : (∏ p ∈ hi, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤ log z₂ / log 1024 * (3 : ℝ) ^ 15 :=
        hhi.trans (mul_le_mul_of_nonneg_left (goldbach_exp_large (le_refl 1024)) (by positivity))
      have hr : log z₂ / log 1024 ≤ log z₂ / log z₁ :=
        div_le_div_of_nonneg_left hL₂.le hL (Real.log_le_log (by linarith only [hz₁]) hzlo)
      calc
        _ = (∏ p ∈ lo, (1 - 1 / ((p : ℝ) - 1))⁻¹) *
            (∏ p ∈ hi, (1 - 1 / ((p : ℝ) - 1))⁻¹) :=
          (Finset.prod_filter_mul_prod_filter_not s (fun p => p < 1024) _).symm
        _ ≤ 1024 * (log z₂ / log 1024 * (3 : ℝ) ^ 15) :=
          mul_le_mul hlo hb (Finset.prod_nonneg (fun p hp => (inv_pos.mpr (goldbach_factor_positive (hs p (Finset.mem_filter.mp hp).1).2)).le)) (by norm_num)
        _ = log z₂ / log 1024 * (1024 * (3 : ℝ) ^ 15) := by ring
        _ ≤ log z₂ / log z₁ * (1 + (10 : ℝ) ^ 12 / log z₁) :=
          mul_le_mul hr hlinear (by positivity) (by positivity)

#print axioms numerical_goldbach_split_interval
end ChenEffective
