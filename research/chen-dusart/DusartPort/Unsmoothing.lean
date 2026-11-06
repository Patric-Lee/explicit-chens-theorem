/- Selectively adapted from LeanLab, commit 2fdf0dc222e35d60ab0043d4597b68ebc2abe4cb.
Apache 2.0; original project contributors. Only the elementary definitions
and unsmoothing proof are included; no RH or cited numerical premises. -/
import Mathlib
noncomputable section
namespace ChenEffective.Dusart
open Real Finset
open scoped ArithmeticFunction.vonMangoldt
set_option maxHeartbeats 2000000

def psiF (y : ℝ) : ℝ := ∑ n ∈ Iic ⌊y⌋₊, Λ n

def psi1 (y : ℝ) : ℝ := ∑ n ∈ Iic ⌊y⌋₊, (y - n) * Λ n

theorem psiF_eq_chebyshev (x : ℝ) : psiF x = Chebyshev.psi x := by
  have heq : Finset.Icc (0 : ℕ) ⌊x⌋₊ = Finset.Iic ⌊x⌋₊ := by ext n; simp
  rw [Chebyshev.psi_eq_sum_Icc, heq]
  rfl
theorem psi1_ext {y : ℝ} (hy : 0 ≤ y) {N : ℕ} (hN : ⌊y⌋₊ ≤ N) :
    ∑ n ∈ Iic N, max (y - n) 0 * Λ n = psi1 y := by
  unfold psi1
  rw [← Iic_union_Ioc_eq_Iic hN, sum_union (Iic_disjoint_Ioc le_rfl)]
  have h2 : ∑ n ∈ Ioc ⌊y⌋₊ N, max (y - n) 0 * Λ n = 0 := by
    apply sum_eq_zero
    intro n hn
    rw [mem_Ioc] at hn
    have : y < n := by
      have := Nat.lt_floor_add_one y
      have : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn.1
      push_cast at this; linarith
    rw [max_eq_right (by linarith), zero_mul]
  rw [h2, add_zero]
  apply sum_congr rfl
  intro n hn
  rw [mem_Iic] at hn
  have : (n : ℝ) ≤ y := by
    have := Nat.floor_le hy
    have : (n : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hn
    linarith
  rw [max_eq_left (by linarith)]

theorem psi1_diff_bounds {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h) :
    h * psiF x ≤ psi1 (x + h) - psi1 x ∧ psi1 (x + h) - psi1 x ≤ h * psiF (x + h) := by
  set M := ⌊x + h⌋₊ with hM
  have hxM : ⌊x⌋₊ ≤ M := Nat.floor_le_floor (by linarith)
  have e1 := psi1_ext (show 0 ≤ x + h by linarith) (le_refl M)
  have e0 := psi1_ext hx hxM
  have hdiff : psi1 (x + h) - psi1 x =
      ∑ n ∈ Iic M, (max (x + h - n) 0 - max (x - n) 0) * Λ n := by
    rw [← e1, ← e0, ← sum_sub_distrib]
    refine sum_congr rfl fun n _ => by ring
  have hΛ : ∀ n : ℕ, 0 ≤ Λ n := fun n => ArithmeticFunction.vonMangoldt_nonneg
  constructor
  · -- lower: the terms with n ≤ ⌊x⌋ have weight exactly h
    rw [hdiff]
    have hsub : Iic ⌊x⌋₊ ⊆ Iic M := Iic_subset_Iic.2 hxM
    have hpsi : h * psiF x = ∑ n ∈ Iic ⌊x⌋₊, (max (x + h - n) 0 - max (x - n) 0) * Λ n := by
      unfold psiF
      rw [mul_sum]
      refine sum_congr rfl fun n hn => ?_
      rw [mem_Iic] at hn
      have hn' : (n : ℝ) ≤ x := by
        have : (n : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hn
        exact this.trans (Nat.floor_le hx)
      rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring
    rw [hpsi]
    apply sum_le_sum_of_subset_of_nonneg hsub
    intro n _ _
    apply mul_nonneg _ (hΛ n)
    have : max (x - n) 0 ≤ max (x + h - n) 0 := max_le_max (by linarith) le_rfl
    linarith
  · -- upper: every weight grows by at most h
    rw [hdiff]
    unfold psiF
    rw [← hM, mul_sum]
    refine sum_le_sum fun n _ => ?_
    apply mul_le_mul_of_nonneg_right _ (hΛ n)
    rcases le_total (x - n) 0 with h1 | h1
    · rw [max_eq_right h1]
      rcases le_total (x + h - n) 0 with h2 | h2
      · rw [max_eq_right h2]; linarith
      · rw [max_eq_left h2]; linarith
    · rw [max_eq_left h1, max_eq_left (by linarith)]; linarith


theorem numerical_unsmoothing {x : ℝ} (hx : (3 : ℝ) ^ (120 : ℕ) ≤ x)
    (hΨ : ∀ y : ℝ, (3 : ℝ) ^ (100 : ℕ) ≤ y →
      |psi1 y - y ^ 2 / 2| ≤ (121 / 1000) * y ^ (15 / 8 : ℝ)) :
    |Chebyshev.psi x - x| ≤ (7 / 10) * x ^ (15 / 16 : ℝ) := by
  let v := x ^ (15 / 16 : ℝ)
  let h := (7 / 10 : ℝ) * v
  have hx1 : 1 ≤ x := (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)).trans hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hv : 0 < v := Real.rpow_pos_of_pos hx0 _
  have hh : 0 < h := by dsimp [h]; positivity
  have hx112 : (3 : ℝ) ^ (112 : ℕ) ≤ x :=
    (pow_le_pow_right₀ (by norm_num) (by norm_num : 112 ≤ 120)).trans hx
  have hroot : (700 : ℝ) ≤ x ^ (1 / 16 : ℝ) := by
    have hc : ((3 : ℝ) ^ (112 : ℕ)) ^ (1 / 16 : ℝ) = (3 : ℝ) ^ (7 : ℕ) := by
      rw [← Real.rpow_natCast (3 : ℝ) 112, ← Real.rpow_mul (by norm_num)]
      norm_num
    calc
      _ ≤ (3 : ℝ) ^ (7 : ℕ) := by norm_num
      _ = _ := hc.symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hx112 (by norm_num)
  have hmul : v * x ^ (1 / 16 : ℝ) = x := by
    dsimp [v]
    rw [← Real.rpow_add hx0]
    norm_num
  have hrel : h ≤ x / 1000 := by
    have hp := mul_le_mul_of_nonneg_left hroot hv.le
    rw [hmul] at hp
    dsimp [h]
    linarith only [hp]
  have hx100 : (3 : ℝ) ^ (100 : ℕ) ≤ x :=
    (pow_le_pow_right₀ (by norm_num) (by norm_num : 100 ≤ 120)).trans hx
  have hdown100 : (3 : ℝ) ^ (100 : ℕ) ≤ x - h := by
    have hx101 : (3 : ℝ) ^ (101 : ℕ) ≤ x :=
      (pow_le_pow_right₀ (by norm_num) (by norm_num : 101 ≤ 120)).trans hx
    norm_num at hx101 ⊢
    linarith only [hx101, hrel]
  have hdown0 : 0 ≤ x - h := (pow_nonneg (by norm_num) 100).trans hdown100
  have hv2 : v ^ 2 = x ^ (15 / 8 : ℝ) := by
    dsimp [v]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hup : (x + h) ^ (15 / 8 : ℝ) ≤ (1003 / 1000) * x ^ (15 / 8 : ℝ) := by
    calc
      _ ≤ ((1001 / 1000) * x) ^ (15 / 8 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by linarith only [hrel]) (by norm_num)
      _ = (1001 / 1000 : ℝ) ^ (15 / 8 : ℝ) * x ^ (15 / 8 : ℝ) :=
        Real.mul_rpow (by norm_num) hx0.le
      _ ≤ (1001 / 1000 : ℝ) ^ (2 : ℝ) * x ^ (15 / 8 : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le
            (by norm_num : (1 : ℝ) ≤ 1001 / 1000) (by norm_num : (15 / 8 : ℝ) ≤ 2))
          (by positivity)
      _ ≤ _ := by
        norm_num only [Real.rpow_two]
        exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hdown : (x - h) ^ (15 / 8 : ℝ) ≤ x ^ (15 / 8 : ℝ) :=
    Real.rpow_le_rpow hdown0 (by linarith only [hh]) (by norm_num)
  have h0 := abs_le.mp (hΨ x hx100)
  have hplus := abs_le.mp (hΨ (x + h) (by linarith only [hx100, hh]))
  have hminus := abs_le.mp (hΨ (x - h) hdown100)
  have hdU := (psi1_diff_bounds hx0.le hh).1
  have hdL := (psi1_diff_bounds hdown0 hh).2
  rw [sub_add_cancel] at hdL
  dsimp only [h] at h0 hplus hminus hdU hdL hup hdown
  rw [← psiF_eq_chebyshev]
  apply abs_le.mpr
  constructor
  · have hp : h * (x - (7 / 10) * v) ≤ h * psiF x := by
      dsimp [h] at hdL ⊢
      nlinarith only [hdL, h0.1, hminus.2, hdown, hv2]
    have hh' := (mul_le_mul_iff_right₀ hh).mp hp
    linarith only [hh']
  · have hp : h * psiF x ≤ h * (x + (7 / 10) * v) := by
      dsimp [h] at hdU ⊢
      nlinarith only [hdU, h0.1, hplus.2, hup, hv2]
    have hh' := (mul_le_mul_iff_right₀ hh).mp hp
    linarith only [hh']

#print axioms numerical_unsmoothing

theorem theta_of_numerical_psi {x : ℝ} (hx : (3 : ℝ) ^ (120 : ℕ) ≤ x)
    (hψ : |Chebyshev.psi x - x| ≤ (7 / 10) * x ^ (15 / 16 : ℝ)) :
    |Chebyshev.theta x - x| ≤ (3 / 4) * x ^ (15 / 16 : ℝ) := by
  have hx1 : 1 ≤ x := (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)).trans hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hp : (160 : ℝ) ≤ x ^ (3 / 16 : ℝ) := by
    have hc : ((3 : ℝ) ^ (120 : ℕ)) ^ (1 / 8 : ℝ) = (3 : ℝ) ^ (15 : ℕ) := by
      rw [← Real.rpow_natCast (3 : ℝ) 120, ← Real.rpow_mul (by norm_num)]
      norm_num
    calc
      _ ≤ (3 : ℝ) ^ (15 : ℕ) := by norm_num
      _ = _ := hc.symm
      _ ≤ x ^ (1 / 8 : ℝ) := Real.rpow_le_rpow (by positivity) hx (by norm_num)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hlog : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
    have hh := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 4)
    linarith only [hh]
  have hprod : Real.sqrt x * x ^ (1 / 4 : ℝ) = x ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
    norm_num
  have hsmall : 2 * Real.sqrt x * Real.log x ≤ (1 / 20) * x ^ (15 / 16 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hx0.le (3 / 4 : ℝ))
    have heq : x ^ (3 / 4 : ℝ) * x ^ (3 / 16 : ℝ) = x ^ (15 / 16 : ℝ) := by
      rw [← Real.rpow_add hx0]
      norm_num
    rw [heq] at hh
    calc
      _ ≤ 2 * Real.sqrt x * (4 * x ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 8 * x ^ (3 / 4 : ℝ) := by nlinarith only [hprod]
      _ ≤ _ := by linarith only [hh]
  have hd := (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx1).trans hsmall
  have ht := abs_add_le (Chebyshev.theta x - Chebyshev.psi x) (Chebyshev.psi x - x)
  rw [sub_add_sub_cancel, abs_sub_comm (Chebyshev.theta x) (Chebyshev.psi x)] at ht
  linarith only [ht, hd, hψ]

#print axioms theta_of_numerical_psi
end ChenEffective.Dusart
