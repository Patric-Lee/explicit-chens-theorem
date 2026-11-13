import BJSSelbergSignedMoment
import BJSHarmonicKernel

noncomputable section
namespace ChenEffective
open Real Finset
open MathlibNt.SieveTheory LiuWeight SingularSeries
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def selbergTwoTermResidualTerm (N R d : ℕ) : ℝ :=
  liuSelbergCorrection N d*
    (realHarmonic ((R:ℝ)/d)-log ((R:ℝ)/d)-eulerMascheroniConstant)

def selbergTwoTermResidual (N R : ℕ) : ℝ := ∑' d,selbergTwoTermResidualTerm N R d

theorem selberg_harmonic_convolution_summable (N R : ℕ) :
    Summable (fun d : ℕ => liuSelbergCorrection N d*realHarmonic ((R:ℝ)/d)) := by
  apply summable_of_ne_finset_zero (s:=Icc 1 R)
  intro d hd
  by_cases hd0 : d=0
  · subst d; simp
  have hRd : R<d := by simp only [mem_Icc,not_and_or] at hd; omega
  have hdp : (0:ℝ)<d := by exact_mod_cast (Nat.pos_of_ne_zero hd0)
  rw [real_harmonic_zero_below_one ((div_lt_one hdp).mpr (by exact_mod_cast hRd)),mul_zero]

theorem selberg_two_term_residual_summable {N R : ℕ}
    (hEven : Even N) (hN : 0<N) (hR : 1≤R) :
    Summable (selbergTwoTermResidualTerm N R) := by
  have hc : Summable (liuSelbergCorrection N) :=
    Summable.of_norm (by simpa only [Real.norm_eq_abs] using summable_abs_liuSelbergCorrection hEven hN)
  have hl : Summable (fun d => liuSelbergCorrection N d*log (d:ℝ)) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (log_natCast_nonneg _)] using
      summable_abs_liuSelbergCorrection_mul_log_nat hEven hN
  have hRp : (0:ℝ)<R := by exact_mod_cast (show 0<R by omega)
  apply ((selberg_harmonic_convolution_summable N R).sub (hc.mul_right
    (log (R:ℝ)+eulerMascheroniConstant))).add hl |>.congr
  intro d
  by_cases hd : d=0
  · subst d; simp [selbergTwoTermResidualTerm]
  have hdp : (0:ℝ)<d := by exact_mod_cast (Nat.pos_of_ne_zero hd)
  unfold selbergTwoTermResidualTerm
  rw [log_div hRp.ne' hdp.ne']
  ring

theorem selberg_two_term_identity {N R : ℕ}
    (hEven : Even N) (hN : 0<N) (hR : 1≤R) :
    (∑ n∈Icc 1 R,liuSelbergArithmetic N n) =
      (log (R:ℝ)+selbergSpecializedSecondary N)/(2*liuSingularSeries N)+
        selbergTwoTermResidual N R := by
  have hc : Summable (liuSelbergCorrection N) :=
    Summable.of_norm (by simpa only [Real.norm_eq_abs] using summable_abs_liuSelbergCorrection hEven hN)
  have hl : Summable (fun d => liuSelbergCorrection N d*log (d:ℝ)) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (log_natCast_nonneg _)] using
      summable_abs_liuSelbergCorrection_mul_log_nat hEven hN
  have hRp : (0:ℝ)<R := by exact_mod_cast (show 0<R by omega)
  have heq (d : ℕ) : selbergTwoTermResidualTerm N R d =
      liuSelbergCorrection N d*realHarmonic ((R:ℝ)/d)-
      liuSelbergCorrection N d*(log (R:ℝ)+eulerMascheroniConstant)+
      liuSelbergCorrection N d*log (d:ℝ) := by
    by_cases hd : d=0
    · subst d; simp [selbergTwoTermResidualTerm]
    have hdp : (0:ℝ)<d := by exact_mod_cast (Nat.pos_of_ne_zero hd)
    unfold selbergTwoTermResidualTerm
    rw [log_div hRp.ne' hdp.ne']
    ring
  have hfinite : (∑' d,liuSelbergCorrection N d*realHarmonic ((R:ℝ)/d))=
      ∑ d∈Icc 1 R,liuSelbergCorrection N d*liuHarmonic (R/d) := by
    rw [tsum_eq_sum (s:=Icc 1 R) (by
      intro d hd
      by_cases hd0 : d=0
      · subst d; simp
      have hRd : R<d := by simp only [mem_Icc,not_and_or] at hd; omega
      have hdp : (0:ℝ)<d := by exact_mod_cast (Nat.pos_of_ne_zero hd0)
      rw [real_harmonic_zero_below_one ((div_lt_one hdp).mpr (by exact_mod_cast hRd)),mul_zero])]
    apply sum_congr rfl
    intro d hd
    simp only [realHarmonic,Nat.floor_div_natCast,Nat.floor_natCast]
  have hres : selbergTwoTermResidual N R =
      (∑ n∈Icc 1 R,liuSelbergArithmetic N n)-
      (log (R:ℝ)+eulerMascheroniConstant)/(2*liuSingularSeries N)+
      ∑' d,liuSelbergCorrection N d*log (d:ℝ) := by
    unfold selbergTwoTermResidual
    simp_rw [heq]
    rw [((selberg_harmonic_convolution_summable N R).sub (hc.mul_right _)).tsum_add hl,
      (selberg_harmonic_convolution_summable N R).tsum_sub (hc.mul_right _),
      tsum_mul_right,hfinite,← liuSelbergArithmetic_sum_Icc N R,
      tsum_liuSelbergCorrection hEven hN]
    ring
  rw [selberg_signed_log_moment hEven hN] at hres
  unfold selbergSpecializedSecondary
  linear_combination -hres

#print axioms selberg_two_term_identity
end ChenEffective
