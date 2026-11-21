import BJSExpandedDenominator
import GRH14ErrorBudget

/-! The actual Selberg denominator at the H<14 target, uniformly in the
sieving radius parameter. These statements are unconditional. They remove
the restriction to the old fixed epsilon; they do not assert the complete
triple count, whose off-diagonal and prime-pair errors still need work. -/
noncomputable section
namespace ChenEffective.GRH14
open Real Finset
open MathlibNt.SieveTheory LiuWeight SingularSeries
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
theorem normalized_error {N R : ℕ} {ε : ℝ} (hε : ε ≤ 1/1000)
    (hN : 0<N) (hL : (1000000:ℝ)≤log (N:ℝ)) (hR : 1≤R)
    (hlogR : (1/4-ε/2)*log (N:ℝ)-log 2≤log (R:ℝ)) :
    ((20/sqrt R)*exp (1096+log (N:ℝ)/16))*liuSingularSeries N≤1 := by
  have hRp : (0:ℝ)<R := by exact_mod_cast (show 0<R by omega)
  have hroot : 1/sqrt (R:ℝ)=exp (-log (R:ℝ)/2) := by
    rw [sqrt_eq_rpow,rpow_def_of_pos hRp,one_div,← exp_neg]
    congr 1
    ring
  have hlog2 : log (2:ℝ)≤1 := by linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have he : 1096+log (N:ℝ)/16+(822+3*log (N:ℝ)/64)-log (R:ℝ)/2≤-20 := by
    have hεL := mul_le_mul_of_nonneg_right hε (show 0 ≤ log (N:ℝ) by linarith only [hL])
    linarith only [hL,hlogR,hlog2,hεL]
  have h20 : (20:ℝ)≤exp 20 := by linarith only [add_one_le_exp (20:ℝ)]
  calc
    _ ≤ ((20/sqrt R)*exp (1096+log (N:ℝ)/16))*exp (822+3*log (N:ℝ)/64) :=
      mul_le_mul_of_nonneg_left (expanded_singular_series_cap hN) (by positivity)
    _ = 20*exp (1096+log (N:ℝ)/16+(822+3*log (N:ℝ)/64)-log (R:ℝ)/2) := by
      rw [show (20:ℝ)/sqrt R=20*(1/sqrt R) by ring,hroot]
      calc
        _ = 20*(exp (-log (R:ℝ)/2)*exp (1096+log (N:ℝ)/16)*
            exp (822+3*log (N:ℝ)/64)) := by ring
        _ = _ := by rw [← exp_add,← exp_add]; congr 1; ring
    _ ≤ 20*exp (-20:ℝ) := mul_le_mul_of_nonneg_left (exp_le_exp.mpr he) (by norm_num)
    _ ≤ 1 := by
      have hh := mul_le_mul_of_nonneg_right h20 (exp_pos (-20:ℝ)).le
      rw [← exp_add] at hh
      norm_num at hh
      exact hh

theorem denominator_81_of_log {N : ℕ} {ε : ℝ} (hε : ε ≤ 1/1000)
    (hL : (1000000:ℝ)≤log (N:ℝ)) (hEven : Even N) :
    log (N:ℝ)/((81/10:ℝ)*liuSingularSeries N)≤liuSelbergDenominator N ε := by
  have hn : 0<N := by
    by_contra h
    have hh : N=0 := by omega
    subst N
    norm_num at hL
  have hnR : (0:ℝ)<N := by exact_mod_cast hn
  have hN256 : 256≤N := by
    have hh := log_le_sub_one_of_pos hnR
    exact_mod_cast (by linarith only [hh,hL] : (256:ℝ)≤N)
  obtain ⟨hlogR,hR⟩ := numerical_selberg_log_floor hN256
    (show (1/8:ℝ)≤1/4-ε/2 by linarith only [hε])
  change 2≤paperQSourceCutoff N ε at hR
  change (1/4-ε/2)*log (N:ℝ)-log 2≤log (paperQSourceCutoff N ε:ℝ) at hlogR
  have hexp := selberg_uniform_two_term_expansion hEven hn (show 1≤paperQSourceCutoff N ε by omega)
  rw [← liuSelbergDenominator_eq_sum_Icc hEven (by omega)] at hexp
  have hlo := (abs_le.mp hexp).1
  have hSp := liuSingularSeries_pos N
  have hmul := mul_le_mul_of_nonneg_right hlo hSp.le
  have herr := normalized_error hε hn hL (show 1≤paperQSourceCutoff N ε by omega) hlogR
  have hc := (selberg_specialized_secondary_pos N).le
  have hmain : ((log (paperQSourceCutoff N ε:ℝ)+selbergSpecializedSecondary N)/
      (2*liuSingularSeries N))*liuSingularSeries N=
      (log (paperQSourceCutoff N ε:ℝ)+selbergSpecializedSecondary N)/2 := by field_simp
  rw [sub_mul,hmain] at hmul
  apply (div_le_iff₀ (mul_pos (by norm_num) hSp)).mpr
  have hl2 : log (2:ℝ)≤1 := by linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hεL := mul_le_mul_of_nonneg_right hε (show 0≤log (N:ℝ) by linarith only [hL])
  nlinarith only [hmul,herr,hc,hlogR,hL,hl2,hεL]


theorem denominator_at_target {N : ℕ} (hN : targetCutoff ≤ N)
    (hEven : Even N) {ε : ℝ} (hε : ε ≤ 1/1000) :
    log (N:ℝ)/((81/10:ℝ)*liuSingularSeries N) ≤ liuSelbergDenominator N ε :=
  denominator_81_of_log hε (target_log_lower hN) hEven

#print axioms denominator_at_target
end ChenEffective.GRH14
