import NumericalSelbergEulerMajorant

noncomputable section
namespace ChenEffective
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiuWeight
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem numerical_selberg_root_local (p : Nat.Primes) (hpd : ¬(p : ℕ) ∣ 2) :
    ‖selbergRootWeight p‖+‖selbergRootWeight ((p : ℕ)^2)‖ ≤
      9*((p : ℝ)*Real.sqrt (p : ℕ))⁻¹ := by
  let f : ℕ → ℝ := selbergRootWeight
  change ‖f p‖+‖f ((p : ℕ)^2)‖ ≤ _
  have hp2 : 2 < (p : ℕ) := by
    have hpne : (p : ℕ) ≠ 2 := by
      intro he
      apply hpd
      rw [he]
    exact lt_of_le_of_ne p.2.two_le hpne.symm
  let P : ℝ := (p : ℕ)
  let s : ℝ := Real.sqrt P
  let r : ℝ := Real.sqrt s
  have hpR : 0 < P := by
    dsimp only [P]
    exact_mod_cast p.2.pos
  have hpR2 : 0 < P - 2 := by
    dsimp only [P]
    exact sub_pos.mpr (by exact_mod_cast hp2)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr (by
    dsimp only [P]
    exact_mod_cast p.2.one_lt.le)
  have hs_sq : s ^ 2 = P := Real.sq_sqrt hpR.le
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr_sq : r ^ 2 = s := Real.sq_sqrt hs0
  have hrle : r ≤ s := by nlinarith [sq_nonneg (s - r)]
  have hden : 0 < P * (P - 2) := mul_pos hpR hpR2
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hs1
  have hfp : ‖f (p : ℕ)‖ = 2 / (P * (P - 2)) * r := by
    simp only [f, selbergRootWeight, liuSelbergCorrection_prime_of_not_dvd (by norm_num : Even (2 : ℕ)) p.2 hpd,
      Real.norm_eq_abs, abs_mul, abs_abs, abs_div]
    norm_num
    rw [abs_of_pos hpR2, abs_of_nonneg hr0]
  have hfp2 : ‖f ((p : ℕ) ^ 2)‖ = 1 / (P * (P - 2)) * s := by
    simp only [f, selbergRootWeight, liuSelbergCorrection_prime_sq_of_not_dvd p.2 hpd,
      Real.norm_eq_abs, abs_mul, abs_abs, abs_div]
    norm_num
    rw [abs_of_pos hpR2, abs_of_nonneg hs0]
  rw [hfp, hfp2]
  change 2 / (P * (P - 2)) * r + 1 / (P * (P - 2)) * s ≤
    9 * (P * s)⁻¹
  rw [show 2 / (P * (P - 2)) * r + 1 / (P * (P - 2)) * s =
    (2 * r + s) / (P * (P - 2)) by field_simp]
  rw [show 9 * (P * s)⁻¹ = 9 / (P * s) by simp [div_eq_mul_inv]]
  rw [div_le_div_iff₀ hden (mul_pos hpR hspos)]
  have hnum : 2 * r + s ≤ 3 * s := by linarith
  have hmul := mul_le_mul_of_nonneg_right hnum (mul_nonneg hpR.le hs0)
  have hp3 : (3 : ℝ) ≤ P := by
    dsimp only [P]
    exact_mod_cast (Nat.succ_le_iff.mpr hp2)
  nlinarith [sq_nonneg P]

theorem selbergRootWeight_nonneg (n : ℕ) : 0 ≤ selbergRootWeight n := by
  unfold selbergRootWeight
  positivity

theorem selbergRootWeight_local_sum (p : ℕ) (hp : p.Prime) :
    (∑' e, selbergRootWeight (p^e)) = 1+selbergRootWeight p+selbergRootWeight (p^2) := by
  rw [tsum_eq_sum (s := range 3)]
  · rw [Finset.sum_range_succ (n := 2), Finset.sum_range_succ (n := 1), Finset.sum_range_succ (n := 0)]
    simp [selbergRootWeight, liuSelbergCorrection_one]
  · intro e he
    have he3 : 3 ≤ e := by simpa only [mem_range, not_lt] using he
    unfold selbergRootWeight
    by_cases hpd : p ∣ 2
    · rw [liuSelbergCorrection_prime_pow_eq_zero_of_dvd hp hpd (by omega)]
      simp
    · rw [liuSelbergCorrection_prime_pow_eq_zero_of_not_dvd hp hpd he3]
      simp

theorem numerical_selberg_root_factor (p : ℕ) (hp : p.Prime) :
    (∑' e, selbergRootWeight (p^e)) ≤ Real.exp (selbergRootMajorant p) := by
  rw [selbergRootWeight_local_sum p hp]
  apply le_trans _ (by simpa only [add_comm] using Real.add_one_le_exp (selbergRootMajorant p))
  have hroot0 := selbergRootWeight_nonneg p
  have hroot2 := selbergRootWeight_nonneg (p^2)
  by_cases hpd : p ∣ 2
  · have hp2 : p=2 := ((Nat.dvd_prime Nat.prime_two).mp hpd).resolve_left hp.ne_one
    subst p
    have hsq : selbergRootWeight (2^2)=0 := by
      unfold selbergRootWeight
      rw [liuSelbergCorrection_prime_pow_eq_zero_of_dvd Nat.prime_two (dvd_refl 2) (by norm_num)]
      simp
    have hr : Real.sqrt (Real.sqrt (2 : ℝ)) ≤ 2 := by
      apply (Real.sqrt_le_iff).mpr
      constructor
      · norm_num
      · apply (Real.sqrt_le_iff).mpr
        norm_num
    have ht : selbergRootWeight 2 ≤ 2 := by
      unfold selbergRootWeight
      rw [liuSelbergCorrection_prime_of_dvd Nat.prime_two (dvd_refl 2)]
      norm_num only [Nat.cast_ofNat, abs_neg, abs_inv, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith only [hr, Real.sqrt_nonneg (Real.sqrt (2 : ℝ))]
    have hb : (2 : ℝ) ≤ selbergRootMajorant 2 := by unfold selbergRootMajorant; simp; positivity
    linarith only [hsq, ht, hb]
  · have hh := numerical_selberg_root_local ⟨p,hp⟩ hpd
    simp only [Real.norm_eq_abs, abs_of_nonneg (selbergRootWeight_nonneg _)] at hh
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have he : (p : ℝ)^(-(3/2 : ℝ)) = ((p : ℝ)*Real.sqrt p)⁻¹ := by
      rw [Real.rpow_neg hp0.le, show (3/2 : ℝ)=1+1/2 by norm_num,
        Real.rpow_add hp0, Real.rpow_one, ← Real.sqrt_eq_rpow]
    have hp2 : p ≠ 2 := by
      intro he
      apply hpd
      rw [he]
    simp only [selbergRootMajorant, if_neg hp2, zero_add, he]
    linarith only [hh]

theorem numerical_selberg_root_summable_mass : Summable selbergRootWeight ∧ (∑' n, selbergRootWeight n) ≤ Real.exp 29 := by
  apply numerical_multiplicative_mass selbergRootWeight selbergRootMajorant 29
    (by simp [selbergRootWeight]) (by simp [selbergRootWeight, liuSelbergCorrection_one])
    selbergRootWeight_nonneg
  · intro m n hmn
    simp only [selbergRootWeight, (liuSelbergCorrection_isMultiplicative 2).map_mul_of_coprime hmn,
      abs_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m),
      Real.sqrt_mul (Real.sqrt_nonneg (m : ℝ))]
    ring
  · intro p hp
    apply summable_of_ne_finset_zero (s := range 3)
    intro e he
    have he3 : 3 ≤ e := by simpa only [mem_range, not_lt] using he
    unfold selbergRootWeight
    by_cases hpd : p ∣ 2
    · rw [liuSelbergCorrection_prime_pow_eq_zero_of_dvd hp hpd (by omega)]
      simp
    · rw [liuSelbergCorrection_prime_pow_eq_zero_of_not_dvd hp hpd he3]
      simp
  · exact selbergRootMajorant_summable
  · intro n
    unfold selbergRootMajorant
    positivity
  · exact selbergRootMajorant_mass
  · exact numerical_selberg_root_factor

theorem numerical_selberg_root_mass : (∑' n, selbergRootWeight n) ≤ Real.exp 29 := numerical_selberg_root_summable_mass.2

#print axioms numerical_selberg_root_mass
end ChenEffective
