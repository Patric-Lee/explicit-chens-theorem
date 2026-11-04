import NumericalSourceMass

noncomputable section
namespace ChenEffective
open Real Finset Filter
open MathlibNt.SieveTheory SingularSeries
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem universal_product_step (m : ℕ) :
    liuUniversalProductTruncated (m+1) = liuUniversalProductTruncated m*(1+liuBaseDeviation (m+1)) := by
  unfold liuUniversalProductTruncated
  rw [Finset.prod_range_succ]

theorem universal_product_finite_tail {z : ℕ} (hz : 2 ≤ z) (k : ℕ) :
    liuUniversalProductTruncated z*((z : ℝ)-1)/z ≤
      liuUniversalProductTruncated (z+k)*(((z+k : ℕ) : ℝ)-1)/(z+k : ℕ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    let m := z+k
    have hm : 2 ≤ m := by dsimp [m]; omega
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hm0 : (0 : ℝ) < m := by linarith only [hmR]
    have hg : 1-1/(m : ℝ)^2 ≤ 1+liuBaseDeviation (m+1) := by
      unfold liuBaseDeviation
      split_ifs
      · push_cast
        ring_nf
        rfl
      · simp only [add_zero,sub_le_self_iff]
        positivity
    have hP : 0 ≤ liuUniversalProductTruncated m := (liuUniversalProductTruncated_pos m).le
    have hh := mul_le_mul_of_nonneg_left hg hP
    have hnext : liuUniversalProductTruncated m*((m : ℝ)-1)/m ≤
        liuUniversalProductTruncated (m+1)*((m : ℝ)+1-1)/((m : ℝ)+1) := by
      rw [universal_product_step]
      have hmul := mul_le_mul_of_nonneg_right hh
        (show 0 ≤ (m : ℝ)/((m : ℝ)+1) by positivity)
      have heq : liuUniversalProductTruncated m*(1-1/(m : ℝ)^2)*((m : ℝ)/((m : ℝ)+1)) =
          liuUniversalProductTruncated m*((m : ℝ)-1)/m := by field_simp; ring
      rw [heq] at hmul
      simpa only [add_sub_cancel_right,mul_div_assoc] using hmul
    exact ih.trans (by simpa only [m,Nat.add_assoc,Nat.cast_add,Nat.cast_one,add_assoc] using hnext)

/-- A telescoping product over all integers bounds the omitted odd-prime tail. -/
theorem numerical_universal_product_upper {z r : ℕ} (hr : 0 < r) (hz : 2*r ≤ z) :
    liuUniversalProductTruncated z ≤ (1+1/(r : ℝ))*liuUniversalProduct := by
  have hz2 : 2 ≤ z := by omega
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (show 0 < z by omega)
  have hU : liuUniversalProductTruncated z*((z : ℝ)-1)/z ≤ liuUniversalProduct := by
    apply ge_of_tendsto (tendsto_liuUniversalProductTruncated.comp (tendsto_add_atTop_nat z))
    filter_upwards [] with k
    have hh := universal_product_finite_tail hz2 k
    have hP : 0 ≤ liuUniversalProductTruncated (z+k) := (liuUniversalProductTruncated_pos _).le
    have hk : (0 : ℝ) < (z+k : ℕ) := by exact_mod_cast (show 0 < z+k by omega)
    change _ ≤ liuUniversalProductTruncated (k+z)
    rw [Nat.add_comm k z]
    exact hh.trans ((div_le_iff₀ hk).mpr (by nlinarith only [hP]))
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hzr : 2*(r : ℝ) ≤ z := by exact_mod_cast hz
  have hcoef : 1 ≤ (1+1/(r : ℝ))*(((z : ℝ)-1)/z) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hz0).mpr
    have hrr : 1 ≤ (r : ℝ) := by exact_mod_cast hr
    have heq : (1+1/(r : ℝ))*((z : ℝ)-1)*(r : ℝ) = ((r : ℝ)+1)*((z : ℝ)-1) := by field_simp
    apply (mul_le_mul_iff_left₀ hr0).mp
    rw [heq]
    nlinarith only [hzr,hrr]
  have hP : 0 ≤ liuUniversalProductTruncated z := (liuUniversalProductTruncated_pos _).le
  have hmul := mul_le_mul_of_nonneg_left hU (show 0 ≤ 1+1/(r : ℝ) by positivity)
  have hh := mul_le_mul_of_nonneg_right hcoef hP
  apply le_trans _ hmul
  convert hh using 1 <;> ring

theorem numerical_singular_truncated_upper {N z r : ℕ} (hN : 0 < N) (hr : 0 < r) (hz : 2*r ≤ z) :
    liuSingularSeriesTruncated N z ≤ (1+1/(r : ℝ))*liuSingularSeries N := by
  rw [liuSingularSeriesTruncated_factorization,liuSingularSeries]
  calc
    _ ≤ liuCorrection N*liuUniversalProductTruncated z :=
      mul_le_mul_of_nonneg_right (liuCorrectionTruncated_le_liuCorrection N z hN)
        (liuUniversalProductTruncated_pos _).le
    _ ≤ liuCorrection N*((1+1/(r : ℝ))*liuUniversalProduct) :=
      mul_le_mul_of_nonneg_left (numerical_universal_product_upper hr hz) (liuCorrection_pos _).le
    _ = _ := by ring

#print axioms numerical_singular_truncated_upper
end ChenEffective
