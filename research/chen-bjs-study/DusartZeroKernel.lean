import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Algebraic comparison for the absolute smoothed zero sum.
The strip lower bound is explicit. No assertion about actual zeta zeros
or their global sum is made in this module. -/
namespace ChenEffective
set_option maxHeartbeats 2000000

theorem dusart_zero_kernel_polynomial {b y : ℝ}
    (hb : (1 / 8 : ℝ) ≤ b) (hb1 : b ≤ 1) (hy : 0 ≤ y) :
    (b ^ 2 + y) * ((1 - b) ^ 2 + y) ^ 2 ≤
      4 * (b * (1 - b) + y) ^ 2 * ((1 + b) ^ 2 + y) := by
  have hb0 : 0 ≤ b := by linarith only [hb]
  have hbm : 0 ≤ 1 - b := by linarith only [hb1]
  have h2 : 0 ≤ 2 + 20 * b - 7 * b ^ 2 := by
    nlinarith only [mul_nonneg hb0 hbm, hb0]
  have h3 : 0 ≤ -1 + 11 * b + 15 * b ^ 2 + 7 * b ^ 3 := by
    have hp := pow_nonneg hb0 3
    nlinarith only [hb, sq_nonneg b, hp]
  have h4 : 0 ≤ b ^ 2 * (1 - b) ^ 2 * (3 + 10 * b + 3 * b ^ 2) := by positivity
  have hi : 4 * (b * (1 - b) + y) ^ 2 * ((1 + b) ^ 2 + y) -
      (b ^ 2 + y) * ((1 - b) ^ 2 + y) ^ 2 =
      3 * y ^ 3 + (2 + 20 * b - 7 * b ^ 2) * y ^ 2 +
      (1 - b) * (-1 + 11 * b + 15 * b ^ 2 + 7 * b ^ 3) * y +
      b ^ 2 * (1 - b) ^ 2 * (3 + 10 * b + 3 * b ^ 2) := by ring
  have hn : 0 ≤ 3 * y ^ 3 + (2 + 20 * b - 7 * b ^ 2) * y ^ 2 +
      (1 - b) * (-1 + 11 * b + 15 * b ^ 2 + 7 * b ^ 3) * y +
      b ^ 2 * (1 - b) ^ 2 * (3 + 10 * b + 3 * b ^ 2) := by positivity
  linarith only [hi, hn]

#print axioms dusart_zero_kernel_polynomial

/-- A factor-two comparison with the positive Hadamard moment. This
requires only the zero strip, not a finite-height RH verification. -/
theorem dusart_zero_kernel_norm (ρ : ℂ)
    (hlo : (1 / 8 : ℝ) ≤ ρ.re) (hhi : ρ.re ≤ 7 / 8) :
    ‖1 / (ρ * (ρ + 1))‖ ≤ 2 * (1 / ρ + 1 / (1 - ρ)).re := by
  let b := ρ.re
  let y := ρ.im ^ 2
  let A := b ^ 2 + y
  let B := (1 - b) ^ 2 + y
  let C := b * (1 - b) + y
  let d := (1 + b) ^ 2 + y
  let n := ‖ρ‖ * ‖ρ + 1‖
  have hb : 0 < b := by dsimp [b]; linarith only [hlo]
  have hbm : 0 < 1 - b := by dsimp [b]; linarith only [hhi]
  have hy : 0 ≤ y := sq_nonneg _
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hn : 0 < n := by
    dsimp [n]
    apply mul_pos (norm_pos_iff.mpr _) (norm_pos_iff.mpr _)
    · intro h; norm_num [h] at hlo
    · intro h
      have hh := congrArg Complex.re h
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hh
      linarith only [hh, hlo]
  have hnorm : n ^ 2 = A * d := by
    dsimp [n, A, d, b, y]
    rw [mul_pow, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re,
      Complex.add_im, Complex.one_im, add_zero]
    ring
  have hp := dusart_zero_kernel_polynomial hlo (by linarith only [hhi]) hy
  change A * B ^ 2 ≤ 4 * C ^ 2 * d at hp
  have hs : (A * B) ^ 2 ≤ (2 * C * n) ^ 2 := by
    calc
      _ = A * (A * B ^ 2) := by ring
      _ ≤ A * (4 * C ^ 2 * d) := mul_le_mul_of_nonneg_left hp hA.le
      _ = _ := by rw [mul_pow, hnorm]; ring
  have hle : A * B ≤ 2 * C * n :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp hs
  have hre : (1 / ρ + 1 / (1 - ρ)).re = C / (A * B) := by
    have haeq : Complex.normSq ρ = A := by simp [Complex.normSq_apply, A, b, y, pow_two]
    have hbeq : Complex.normSq (1 - ρ) = B := by
      simp [Complex.normSq_apply, B, b, y, pow_two]
    simp only [one_div, Complex.add_re, Complex.inv_re, haeq, hbeq,
      Complex.sub_re, Complex.one_re]
    change b / A + (1 - b) / B = C / (A * B)
    field_simp [hA.ne', hB.ne']
    dsimp [A, B, C]
    ring
  rw [norm_div, norm_one, norm_mul, hre]
  change 1 / n ≤ 2 * (C / (A * B))
  rw [← mul_div_assoc]
  exact (div_le_div_iff₀ hn (mul_pos hA hB)).mpr (by simpa using hle)

#print axioms dusart_zero_kernel_norm
end ChenEffective
