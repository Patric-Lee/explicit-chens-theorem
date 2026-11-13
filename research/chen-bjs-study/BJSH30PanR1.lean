/- Threshold-specialized companion of research/chen-effective/NumericalPanR1.lean.
The original producer is retained; all modified numerical statements are rechecked. -/
import BJSH30PanNormalization
import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergRemainder

noncomputable section
namespace ChenEffective.H30
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiuWeight
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem numerical_pan_p2 (N : ℕ) :
    liuSourceR1P₂IntervalReciprocalSum N ≤ 1+Real.log (N : ℝ) := by
  calc
    _ ≤ ∑ p ∈ Icc 1 N, (p : ℝ)⁻¹ := by
      unfold liuSourceR1P₂IntervalReciprocalSum
      simp only [one_div]
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hpR, hpP, _⟩ := mem_filter.mp hp
        exact mem_Icc.mpr ⟨hpP.pos, by have := mem_range.mp hpR; omega⟩
      · intros; positivity
    _ = (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ _ := harmonic_le_one_add_log N
theorem numerical_pan_pair
    (N w : ℕ) (hN : 2 ≤ N) :
    PaperQStyleR1PairUniformBound
      N (liuSourceZ10 N) w (liuSourceY3 N) (liuSourceD2 N)
        (5 * (1+Real.log (N : ℝ)) *
          (N : ℝ) ^ (-1 / 10 : ℝ)) := by
  constructor
  · exact mul_nonneg
      (mul_nonneg (by norm_num)
        (by linarith only [Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega))]))
      (Real.rpow_nonneg (by positivity) _)
  intro d hd
  rw [paperQStyleR1Divisors, Finset.mem_filter] at hd
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos
    (Nat.mem_divisors.mp hd.1).1
    (Nat.pos_of_ne_zero (paperQStyleModulus_ne_zero N w))
  have hp₁bound :=
    liuSourceR1P₁DivisorReciprocalSum_le N d hN hdpos hd.2
  have hp₂bound :=
    numerical_pan_p2 N
  have hfactor :
      liuSourceR1RectangularPairReciprocalSum N d ≤
        (5 * (N : ℝ) ^ (-1 / 10 : ℝ)) *
          (1+Real.log (N : ℝ)) := by
    rw [liuSourceR1RectangularPairReciprocalSum_eq_mul]
    exact mul_le_mul hp₁bound hp₂bound
      (liuSourceR1P₂IntervalReciprocalSum_nonneg N)
      (mul_nonneg (by norm_num)
        (Real.rpow_nonneg (by positivity) _))
  calc
    paperQStyleR1PairReciprocalSum
        N (liuSourceZ10 N) (liuSourceY3 N) d ≤
      liuSourceR1RectangularPairReciprocalSum N d :=
        paperQStyleR1PairReciprocalSum_source_le_rectangular N d
    _ ≤ (5 * (N : ℝ) ^ (-1 / 10 : ℝ)) *
        (1+Real.log (N : ℝ)) := hfactor
    _ = 5 * (1+Real.log (N : ℝ)) *
        (N : ℝ) ^ (-1 / 10 : ℝ) := by ring


theorem numerical_pan_r1_divisor (N w : ℕ) (hN : 1 ≤ N) :
    paperQStyleR1DivisorWeightSum N w (liuSourceD2 N) ≤ (1+Real.log (N : ℝ))^6 := by
  apply numerical_totient_weight_mass 3 hN
  · intro d hd
    obtain ⟨hddiv, hdcut⟩ := mem_filter.mp hd
    have hdpos := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hddiv)
      (Nat.pos_of_ne_zero (paperQStyleModulus_ne_zero N w))
    refine mem_Icc.mpr ⟨hdpos, hdcut.trans ?_⟩
    unfold liuSourceD2
    exact Nat.floor_le_of_le (Real.rpow_le_self_of_one_le (by exact_mod_cast hN) (by norm_num))
  · intro d hd
    exact (paperQStyleModulus_squarefree N w).squarefree_of_dvd
      (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)

theorem numerical_pan_r1 (κ : ℝ) (N : ℕ) (ε : ℝ) (hN : 9 ≤ N) (hε : 0 ≤ ε) :
    liuPaperQSourceR1Majorant (liuLogarithmicIntegral κ) N ε ≤
      30*liuLogarithmicIntegralUpperConstant κ*(N : ℝ)^(9/10 : ℝ)*(1+Real.log (N : ℝ))^6 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl := log_one_le_of_eight_le (by omega : 8 ≤ N)
  have hl0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hl
  have hC := liuLogarithmicIntegralUpperConstant_nonneg κ
  have hwy := paperQSourceCutoff_le_floor_cuberoot N ε (by omega) hε
  have hdiv := numerical_pan_r1_divisor N (paperQSourceCutoff N ε) (by omega)
  have hmain := (liuLogarithmicIntegral_paperLiUpperModel κ).paperQStyleSourceR1Majorant_le_divisorWeight_mul
    N (liuSourceZ10 N) (paperQSourceCutoff N ε) (liuSourceY3 N) (liuSourceD2 N)
    (by omega) hwy (numerical_pan_pair N _ (by omega))
  rw [liuPaperQSourceR1Majorant_eq_paperQStyleSourceR1Majorant]
  have hratio : (1+Real.log (N : ℝ))/Real.log (N : ℝ) ≤ 2 :=
    (div_le_iff₀ hl0).mpr (by linarith only [hl])
  have hp : (N : ℝ)*(N : ℝ)^(-1/10 : ℝ) = (N : ℝ)^(9/10 : ℝ) := by
    nth_rw 1 [← Real.rpow_one (N : ℝ)]
    rw [← Real.rpow_add hN0]
    norm_num
  calc
    _ ≤ (3*liuLogarithmicIntegralUpperConstant κ*N/Real.log (N : ℝ))*
        ((1+Real.log (N : ℝ))^6*(5*(1+Real.log (N : ℝ))*(N : ℝ)^(-1/10 : ℝ))) :=
      hmain.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hdiv (by positivity)) (by positivity))
    _ = 15*liuLogarithmicIntegralUpperConstant κ*(N : ℝ)^(9/10 : ℝ)*
        (1+Real.log (N : ℝ))^6*((1+Real.log (N : ℝ))/Real.log (N : ℝ)) := by
      rw [← hp]
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hratio
        (show 0 ≤ 15*liuLogarithmicIntegralUpperConstant κ*(N : ℝ)^(9/10 : ℝ)*
          (1+Real.log (N : ℝ))^6 by positivity)
      calc
        _ ≤ (15*liuLogarithmicIntegralUpperConstant κ*(N : ℝ)^(9/10 : ℝ)*
          (1+Real.log (N : ℝ))^6)*2 := hh
        _ = _ := by ring

#print axioms numerical_pan_r1
end ChenEffective.H30
