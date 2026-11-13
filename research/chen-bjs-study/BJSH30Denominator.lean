import BJSH30Parameters
import BJSExpandedDenominator

noncomputable section
namespace ChenEffective.H30
open Real Finset
open MathlibNt.SieveTheory LiuWeight SingularSeries
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 512

private opaque expandedSelbergCertificate : {n : ℕ // n=3^1000000} := ⟨3^1000000,rfl⟩
def expandedSelbergThreshold : ℕ := expandedSelbergCertificate.1
theorem expandedSelbergThreshold_eq : expandedSelbergThreshold=3^1000000 :=
  expandedSelbergCertificate.2

theorem expanded_selberg_log {N : ℕ} (hN : expandedSelbergThreshold≤N) :
    (1000000:ℝ)≤log (N:ℝ) := by
  rw [expandedSelbergThreshold_eq] at hN
  exact log_ge_power_three (b:=1000000) (N:=N) hN

theorem expanded_selberg_normalized_error {N R : ℕ}
    (hN : 0<N) (hL : (1000000:ℝ)≤log (N:ℝ)) (hR : 1≤R)
    (hlogR : (1/4-squareEpsilon/2)*log (N:ℝ)-log 2≤log (R:ℝ)) :
    ((20/sqrt R)*exp (1096+log (N:ℝ)/16))*liuSingularSeries N≤1 := by
  have hRp : (0:ℝ)<R := by exact_mod_cast (show 0<R by omega)
  have hroot : 1/sqrt (R:ℝ)=exp (-log (R:ℝ)/2) := by
    rw [sqrt_eq_rpow,rpow_def_of_pos hRp,one_div,← exp_neg]
    congr 1
    ring
  have hlog2 : log (2:ℝ)≤1 := by linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have he : 1096+log (N:ℝ)/16+(822+3*log (N:ℝ)/64)-log (R:ℝ)/2≤-20 := by
    norm_num [squareEpsilon,squareEpsilonDenominator] at hlogR
    linarith only [hL,hlogR,hlog2]
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

theorem expanded_selberg_denominator_81_of_log {N : ℕ}
    (hL : (1000000:ℝ)≤log (N:ℝ)) (hEven : Even N) :
    log (N:ℝ)/((82/10:ℝ)*liuSingularSeries N)≤liuSelbergDenominator N squareEpsilon := by
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
    (show (1/8:ℝ)≤1/4-squareEpsilon/2 by norm_num [squareEpsilon,squareEpsilonDenominator])
  change 2≤paperQSourceCutoff N squareEpsilon at hR
  change (1/4-squareEpsilon/2)*log (N:ℝ)-log 2≤log (paperQSourceCutoff N squareEpsilon:ℝ) at hlogR
  have hexp := selberg_uniform_two_term_expansion hEven hn (show 1≤paperQSourceCutoff N squareEpsilon by omega)
  rw [← liuSelbergDenominator_eq_sum_Icc hEven (by omega)] at hexp
  have hlo := (abs_le.mp hexp).1
  have hSp := liuSingularSeries_pos N
  have hmul := mul_le_mul_of_nonneg_right hlo hSp.le
  have herr := expanded_selberg_normalized_error hn hL (show 1≤paperQSourceCutoff N squareEpsilon by omega) hlogR
  have hc := (selberg_specialized_secondary_pos N).le
  have hmain : ((log (paperQSourceCutoff N squareEpsilon:ℝ)+selbergSpecializedSecondary N)/
      (2*liuSingularSeries N))*liuSingularSeries N=
      (log (paperQSourceCutoff N squareEpsilon:ℝ)+selbergSpecializedSecondary N)/2 := by field_simp
  rw [sub_mul,hmain] at hmul
  apply (div_le_iff₀ (mul_pos (by norm_num) hSp)).mpr
  have hl2 : log (2:ℝ)≤1 := by linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hε : squareEpsilon≤1/100 := by norm_num [squareEpsilon,squareEpsilonDenominator]
  have hεL := mul_le_mul_of_nonneg_right hε (show 0≤log (N:ℝ) by linarith only [hL])
  nlinarith only [hmul,herr,hc,hlogR,hL,hl2,hεL]

theorem expanded_selberg_denominator_of_log {N : ℕ}
    (hL : (1000000:ℝ)≤log (N:ℝ)) (hEven : Even N) {K : ℝ} (hK : 82/10≤K) :
    log (N:ℝ)/(K*liuSingularSeries N)≤liuSelbergDenominator N squareEpsilon := by
  apply le_trans _ (expanded_selberg_denominator_81_of_log hL hEven)
  exact div_le_div_of_nonneg_left (log_natCast_nonneg N)
    (mul_pos (by norm_num) (liuSingularSeries_pos N))
    (mul_le_mul_of_nonneg_right hK (liuSingularSeries_pos N).le)

theorem expanded_selberg_denominator {N : ℕ}
    (hN : expandedSelbergThreshold≤N) (hEven : Even N) {K : ℝ} (hK : 82/10≤K) :
    log (N:ℝ)/(K*liuSingularSeries N)≤liuSelbergDenominator N squareEpsilon :=
  expanded_selberg_denominator_of_log (expanded_selberg_log hN) hEven hK

#print axioms expanded_selberg_denominator
end ChenEffective.H30
