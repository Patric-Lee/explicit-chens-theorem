import BJSStudyMertens
import NumericalSelbergDivisorLog

noncomputable section
namespace ChenEffective
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory LiuWeight
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
attribute [local irreducible] logPowerCutoff

@[irreducible] def bjsStudyDivisorThreshold : ℕ := 3^bjsStudyMertensEndpoint

theorem bjsStudy_selberg_divisor_logs {N : ℕ} (hN : bjsStudyDivisorThreshold ≤ N) :
    (bjsStudyMertensEndpoint : ℝ) ≤ Real.log (N:ℝ) ∧ 2 ≤ Real.log (N:ℝ) := by
  unfold bjsStudyDivisorThreshold at hN
  have hh := log_ge_power_three hN
  exact ⟨hh,(by rw [bjsStudyMertensEndpoint_eq]; norm_num : (2:ℝ) ≤ bjsStudyMertensEndpoint).trans hh⟩
theorem bjsStudy_selberg_divisor_product {N : ℕ} (hN : bjsStudyDivisorThreshold ≤ N) :
    liuPrimeDivisorProduct N ≤ 54*(1+Real.log (Real.log (N : ℝ))) := by
  obtain ⟨hM,hl⟩ := bjsStudy_selberg_divisor_logs hN
  have hNpos : 0 < N := by
    by_contra hh
    have he : N=0 := by omega
    subst N
    norm_num at hl
  let y := liuPrimeDivisorCutoff N
  have hNy : Real.log (N : ℝ) ≤ (y : ℝ) := Nat.le_ceil _
  have hy2 : 2 ≤ y := by exact_mod_cast hl.trans hNy
  have hyM' : bjsStudyMertensEndpoint ≤ y := by exact_mod_cast hM.trans hNy
  have hyM : bjsStudyMertensEndpoint ≤ y := hyM'
  have hsmall := (small_prime_divisor_product_le (N := N) (y := y)).trans
    (bjsStudy_mertens_inverse hyM)
  have hlarge := large_prime_divisor_product_le hNpos hy2 hNy
  have hlog2 : (Real.log (2 : ℝ))⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀' (Real.log_pos (by norm_num))]
    linarith only [Real.log_two_gt_d9]
  have he2 : Real.exp (2 : ℝ) ≤ 9 := by
    rw [show (2 : ℝ)=1+1 by norm_num, Real.exp_add]
    nlinarith only [Real.exp_one_lt_d9, Real.exp_pos (1 : ℝ)]
  have hlarge9 := hlarge.trans ((Real.exp_le_exp.mpr hlog2).trans he2)
  have hsplit : liuPrimeDivisorProduct N =
      (N.primeFactors.filter (· ≤ y)).prod (fun p => 1+((p : ℝ)⁻¹))*
      (N.primeFactors.filter (y < ·)).prod (fun p => 1+((p : ℝ)⁻¹)) := by
    rw [liuPrimeDivisorProduct, ← prod_filter_mul_prod_filter_not N.primeFactors (· ≤ y)]
    simp only [not_le]
  rw [hsplit]
  have hly := log_liuPrimeDivisorCutoff_le hl
  calc
    _ ≤ (6*Real.log (y : ℝ))*9 := mul_le_mul hsmall hlarge9 (by positivity)
      (by have hyy : (1 : ℝ) ≤ y := by exact_mod_cast (show 1 ≤ y by omega)
          exact mul_nonneg (by norm_num) (Real.log_nonneg hyy))
    _ ≤ _ := by dsimp [y] at *; linarith only [hly]

theorem bjsStudy_selberg_divisor_logsum {N : ℕ} (hbound : bjsStudyDivisorThreshold ≤ N) :
    liuPrimeDivisorLogSum N ≤ 3*(1+Real.log (Real.log (N : ℝ)))^2 := by
  obtain ⟨_,hlogN2⟩ := bjsStudy_selberg_divisor_logs hbound
  have hN : 0 < N := by
    by_contra hh
    have he : N=0 := by omega
    subst N
    norm_num at hlogN2
  let y := liuPrimeDivisorCutoff N
  have hlogN_le_y : Real.log (N : ℝ) ≤ (y : ℝ) := Nat.le_ceil _
  have hy : 2 ≤ y := by exact_mod_cast hlogN2.trans hlogN_le_y
  have hlogypos : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogy_le := log_liuPrimeDivisorCutoff_le hlogN2
  have hsmall :
      ∑ p ∈ N.primeFactors.filter (· ≤ y), Real.log p / p ≤
        Real.log y * MertensTheorem.primeReciprocalSum y := by
    calc
      _ ≤ ∑ p ∈ N.primeFactors.filter (· ≤ y),
          Real.log y * ((p : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpP := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
        have hl := Real.strictMonoOn_log.monotoneOn
          (show (0 : ℝ) < p by exact_mod_cast hpP.pos)
          (show (0 : ℝ) < y by positivity)
          (by exact_mod_cast (mem_filter.mp hp).2)
        have hinv : 0 ≤ ((p : ℝ)⁻¹) := by positivity
        change Real.log p * (p : ℝ)⁻¹ ≤ Real.log y * (p : ℝ)⁻¹
        exact mul_le_mul_of_nonneg_right hl hinv
      _ ≤ Real.log y * MertensTheorem.primeReciprocalSum y := by
        rw [← Finset.mul_sum]
        apply mul_le_mul_of_nonneg_left _ hlogypos.le
        unfold MertensTheorem.primeReciprocalSum
        have hs : N.primeFactors.filter (· ≤ y) ⊆
            (range (y + 1)).filter Nat.Prime := by
          intro p hp
          simp only [mem_filter, mem_range] at hp ⊢
          exact ⟨Nat.lt_succ_of_le hp.2, Nat.prime_of_mem_primeFactors hp.1⟩
        simpa only [one_div] using
          (Finset.sum_le_sum_of_subset_of_nonneg hs
            (fun p hp₁ hp₂ => (inv_nonneg.mpr (by positivity) :
              0 ≤ ((p : ℝ)⁻¹))))
  have hlarge :
      ∑ p ∈ N.primeFactors.filter (y < ·), Real.log p / p ≤ 1 := by
    calc
      _ ≤ ∑ p ∈ N.primeFactors.filter (y < ·), Real.log p / y := by
        apply Finset.sum_le_sum
        intro p hp
        exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg p)
          (by positivity) (by exact_mod_cast (mem_filter.mp hp).2.le)
      _ = (∑ p ∈ N.primeFactors.filter (y < ·), Real.log p) / y := by
        rw [Finset.sum_div]
      _ ≤ Real.log N / y := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun p hp₁ hp₂ => Real.log_natCast_nonneg p))
          (sum_log_primeFactors_le_log hN)
      _ ≤ 1 := (div_le_one (by positivity)).2 hlogN_le_y
  rw [liuPrimeDivisorLogSum, ← sum_filter_add_sum_filter_not N.primeFactors (· ≤ y)]
  simp only [not_le]
  let u := 1+Real.log (Real.log (N : ℝ))
  have hu : 1 ≤ u := by dsimp [u]; have := Real.log_nonneg (by linarith only [hlogN2] : 1 ≤ Real.log (N : ℝ)); linarith
  have hly : Real.log (y : ℝ) ≤ u := hlogy_le
  calc
    _ ≤ Real.log (y : ℝ)*MertensTheorem.primeReciprocalSum y+1 := add_le_add hsmall hlarge
    _ ≤ Real.log (y : ℝ)*(1+Real.log (y : ℝ))+1 := by
      gcongr
      exact numerical_selberg_prime_reciprocal y
    _ ≤ 3*u^2 := by nlinarith only [hu,hly,hlogypos,sq_nonneg (u-Real.log (y : ℝ)),mul_nonneg (sub_nonneg.mpr hly) hlogypos.le]


#print axioms bjsStudy_selberg_divisor_product
end ChenEffective
