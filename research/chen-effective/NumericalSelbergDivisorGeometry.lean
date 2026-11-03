import NumericalPanNormalization
import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergPrimeDivisorGrowth

noncomputable section
namespace ChenEffective
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory
open LiuWeight
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
theorem log_liuPrimeDivisorCutoff_le {N : ℕ}
    (hlogN2 : 2 ≤ Real.log (N : ℝ)) :
    Real.log (liuPrimeDivisorCutoff N : ℝ) ≤ 1 + Real.log (Real.log N) := by
  let y := liuPrimeDivisorCutoff N
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := le_trans (by norm_num) hlogN2
  have hlogNpos : 0 < Real.log (N : ℝ) := lt_of_lt_of_le (by norm_num) hlogN2
  have hlogN_le_y : Real.log (N : ℝ) ≤ (y : ℝ) := Nat.le_ceil _
  have hyPos : (0 : ℝ) < y := hlogNpos.trans_le hlogN_le_y
  have hy_lt : (y : ℝ) < Real.log N + 1 := Nat.ceil_lt_add_one hlogN0
  have hy_le_two_log : (y : ℝ) ≤ 2 * Real.log N := by linarith
  calc
    Real.log (y : ℝ) ≤ Real.log (2 * Real.log N) :=
      Real.strictMonoOn_log.monotoneOn hyPos (mul_pos (by norm_num) hlogNpos)
        hy_le_two_log
    _ = Real.log 2 + Real.log (Real.log N) := by
      rw [Real.log_mul (by norm_num) hlogNpos.ne']
    _ ≤ 1 + Real.log (Real.log N) := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]

theorem sum_log_primeFactors_le_log {N : ℕ} (hN : 0 < N) :
    ∑ p ∈ N.primeFactors, Real.log p ≤ Real.log N := by
  have hradPos : 0 < ∏ p ∈ N.primeFactors, p := by
    exact Finset.prod_pos fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).pos
  have hradLe : ∏ p ∈ N.primeFactors, p ≤ N :=
    Nat.le_of_dvd hN (Nat.prod_primeFactors_dvd N)
  calc
    ∑ p ∈ N.primeFactors, Real.log p =
        Real.log (∏ p ∈ N.primeFactors, (p : ℝ)) := by
          rw [Real.log_prod]
          intro p hp
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    _ = Real.log (↑(∏ p ∈ N.primeFactors, p) : ℝ) := by
          rw [Nat.cast_prod]
    _ ≤ Real.log (N : ℝ) := by
          apply Real.strictMonoOn_log.monotoneOn
          · show 0 < (↑(∏ p ∈ N.primeFactors, p) : ℝ)
            exact_mod_cast hradPos
          · show 0 < (N : ℝ)
            exact_mod_cast hN
          · exact_mod_cast hradLe

theorem one_add_prime_inv_le_one_sub_prime_inv_inv
    {p : ℕ} (hp : p.Prime) :
    1 + ((p : ℝ)⁻¹) ≤ (1 - ((p : ℝ)⁻¹))⁻¹ := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hden : 0 < 1 - ((p : ℝ)⁻¹) := by
    have : (1 : ℝ) < p := lt_of_lt_of_le (by norm_num) hpR
    exact sub_pos.mpr ((inv_lt_one₀ (by positivity)).2 this)
  have hmul :
      (1 + ((p : ℝ)⁻¹)) * (1 - ((p : ℝ)⁻¹)) ≤ 1 := by
    have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hpR
    field_simp
    nlinarith
  simpa only [one_div] using (le_div_iff₀ hden).2 hmul

theorem one_le_one_sub_prime_inv_inv {p : ℕ} (hp : p.Prime) :
    1 ≤ (1 - ((p : ℝ)⁻¹))⁻¹ := by
  calc
    1 ≤ 1 + ((p : ℝ)⁻¹) := le_add_of_nonneg_right (by positivity)
    _ ≤ (1 - ((p : ℝ)⁻¹))⁻¹ := one_add_prime_inv_le_one_sub_prime_inv_inv hp

theorem small_prime_divisor_product_le
    {N y : ℕ} :
    (N.primeFactors.filter (· ≤ y)).prod (fun p => 1 + ((p : ℝ)⁻¹)) ≤
      (MertensTheorem.primeProduct y)⁻¹ := by
  let P := (range (y + 1)).filter Nat.Prime
  have hsub : N.primeFactors.filter (· ≤ y) ⊆ P := by
    intro p hp
    simp only [mem_filter, mem_range, P] at hp ⊢
    exact ⟨Nat.lt_succ_of_le hp.2, Nat.prime_of_mem_primeFactors hp.1⟩
  calc
    (N.primeFactors.filter (· ≤ y)).prod (fun p => 1 + ((p : ℝ)⁻¹)) ≤
        (N.primeFactors.filter (· ≤ y)).prod
          (fun p => (1 - ((p : ℝ)⁻¹))⁻¹) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        exact one_add_prime_inv_le_one_sub_prime_inv_inv
          (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)
    _ ≤ P.prod (fun p => (1 - ((p : ℝ)⁻¹))⁻¹) := by
      apply Finset.prod_le_prod_of_subset_of_one_le hsub
      · intro p hp
        exact (one_le_one_sub_prime_inv_inv
          (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)).trans' zero_le_one
      · intro p hpP hp
        exact one_le_one_sub_prime_inv_inv (mem_filter.mp hpP).2
    _ = (MertensTheorem.primeProduct y)⁻¹ := by
      rw [Finset.prod_inv_distrib]
      simp [P, MertensTheorem.primeProduct]

theorem large_prime_divisor_reciprocal_sum_le
    {N y : ℕ} (hN : 0 < N) (hy : 2 ≤ y)
    (hlogN : Real.log N ≤ y) :
    ∑ p ∈ N.primeFactors.filter (y < ·), ((p : ℝ)⁻¹) ≤
      (Real.log 2)⁻¹ := by
  have hyR : (0 : ℝ) < y := by positivity
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hpoint : ∀ p ∈ N.primeFactors.filter (y < ·),
      ((p : ℝ)⁻¹) ≤ Real.log p / ((y : ℝ) * Real.log y) := by
    intro p hp
    have hyp : y < p := (mem_filter.mp hp).2
    have hpR : (y : ℝ) ≤ p := by exact_mod_cast hyp.le
    have hlogle : Real.log (y : ℝ) ≤ Real.log (p : ℝ) :=
      Real.strictMonoOn_log.monotoneOn hyR
        (lt_of_lt_of_le hyR hpR) hpR
    have hratio : (1 : ℝ) ≤ Real.log p / Real.log y :=
      (le_div_iff₀ hlogy).2 (by simpa using hlogle)
    calc
      ((p : ℝ)⁻¹) = 1 / (p : ℝ) := (one_div _).symm
      _ ≤ 1 / (y : ℝ) := one_div_le_one_div_of_le hyR hpR
      _ = (1 / (y : ℝ)) * 1 := by ring
      _ ≤ (1 / (y : ℝ)) * (Real.log p / Real.log y) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = Real.log p / ((y : ℝ) * Real.log y) := by field_simp
  calc
    ∑ p ∈ N.primeFactors.filter (y < ·), ((p : ℝ)⁻¹) ≤
        ∑ p ∈ N.primeFactors.filter (y < ·),
          Real.log p / ((y : ℝ) * Real.log y) :=
      Finset.sum_le_sum hpoint
    _ = (∑ p ∈ N.primeFactors.filter (y < ·), Real.log p) /
          ((y : ℝ) * Real.log y) := by rw [Finset.sum_div]
    _ ≤ Real.log N / ((y : ℝ) * Real.log y) := by
      apply div_le_div_of_nonneg_right _ (mul_nonneg hyR.le hlogy.le)
      exact le_trans
        (Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun p hp₁ hp₂ => Real.log_natCast_nonneg p))
        (sum_log_primeFactors_le_log hN)
    _ ≤ (y : ℝ) / ((y : ℝ) * Real.log y) := by
      exact div_le_div_of_nonneg_right hlogN (mul_nonneg hyR.le hlogy.le)
    _ = (Real.log y)⁻¹ := by field_simp
    _ ≤ (Real.log 2)⁻¹ := by
      apply (inv_le_inv₀ hlogy (Real.log_pos (by norm_num))).2
      exact Real.strictMonoOn_log.monotoneOn (by norm_num) hyR
        (by exact_mod_cast hy)

theorem large_prime_divisor_product_le
    {N y : ℕ} (hN : 0 < N) (hy : 2 ≤ y)
    (hlogN : Real.log N ≤ y) :
    (N.primeFactors.filter (y < ·)).prod
        (fun p => 1 + ((p : ℝ)⁻¹)) ≤
      Real.exp ((Real.log 2)⁻¹) := by
  calc
    (N.primeFactors.filter (y < ·)).prod
        (fun p => 1 + ((p : ℝ)⁻¹)) ≤
        (N.primeFactors.filter (y < ·)).prod
          (fun p => Real.exp ((p : ℝ)⁻¹)) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        simpa only [add_comm] using Real.add_one_le_exp ((p : ℝ)⁻¹)
    _ = Real.exp (∑ p ∈ N.primeFactors.filter (y < ·), ((p : ℝ)⁻¹)) := by
      rw [Real.exp_sum]
    _ ≤ Real.exp ((Real.log 2)⁻¹) :=
      Real.exp_le_exp.mpr (large_prime_divisor_reciprocal_sum_le hN hy hlogN)


end ChenEffective
