import GRH14PanCanonical
import BJSH30PanR1

noncomputable section
namespace ChenEffective.GRH14
open Real Finset
open MathlibNt.SieveTheory LiuWeight
open AnalyticNumberTheory.LargeSieve
open NumericalPanHigh AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def selbergRemainderConstant (A : ℕ) : ℝ :=
  panCanonicalConstant A+1920*liuLogarithmicIntegralUpperConstant 2

theorem numerical_selberg_remainder {N : ℕ} (hN : targetCutoff≤N) (lam : ℕ→ℝ)
    (hlam : LiuSelbergLambdaAdmissible N (1/500:ℝ) lam) :
    |liuSelbergRemainder (liuLogarithmicIntegral 2) N (1/500:ℝ) lam| ≤
      selbergRemainderConstant 5*N/Real.log (N:ℝ)^5 := by

  have hNP : logPowerCutoff 110≤N := pan_log_cutoff_at_target (by norm_num) hN
  have hN9 := (logPowerCutoff_nine_le _).trans hNP
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL := log_one_le_of_eight_le (by omega : 8 ≤ N)
  have hl0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL
  have hε : 0 ≤ 1/(500 : ℝ) := by positivity
  have hcop := numerical_pan_canonical hN
  unfold LiuPaperQCoprimeRBound at hcop
  norm_num only [Real.rpow_natCast,Real.rpow_ofNat] at hcop
  have hp := log_pow_le_rpow_inv_explicit (k := 5+6) (m := 10)
    (by norm_num) (le_refl _) hNP
  norm_num only [Nat.cast_ofNat] at hp
  have hscale : (N : ℝ)^(9/10 : ℝ)*Real.log (N : ℝ)^6 ≤ N/Real.log (N : ℝ)^5 := by
    apply (le_div_iff₀ (pow_pos hl0 5)).mpr
    calc
      _ = (N : ℝ)^(9/10 : ℝ)*Real.log (N : ℝ)^(5+6) := by rw [pow_add]; ring
      _ ≤ (N : ℝ)^(9/10 : ℝ)*(N : ℝ)^(1/10 : ℝ) := by gcongr
      _ = _ := by rw [← Real.rpow_add hN0]; norm_num
  have hr := H30.numerical_pan_r1 2 N (1/(500 : ℝ)) hN9 hε
  have hpaid : liuPaperQSourceR1Majorant (liuLogarithmicIntegral 2) N (1/(500 : ℝ)) ≤
      1920*liuLogarithmicIntegralUpperConstant 2*N/Real.log (N : ℝ)^5 := by
    have hC := liuLogarithmicIntegralUpperConstant_nonneg 2
    calc
      _ ≤ 30*liuLogarithmicIntegralUpperConstant 2*(N : ℝ)^(9/10 : ℝ)*
          (1+Real.log (N : ℝ))^6 := hr
      _ ≤ 30*liuLogarithmicIntegralUpperConstant 2*(N : ℝ)^(9/10 : ℝ)*
          (2*Real.log (N : ℝ))^6 := by
        gcongr
        linarith only [hL]
      _ = (1920*liuLogarithmicIntegralUpperConstant 2)*
          ((N : ℝ)^(9/10 : ℝ)*Real.log (N : ℝ)^6) := by ring
      _ ≤ (1920*liuLogarithmicIntegralUpperConstant 2)*(N/Real.log (N : ℝ)^5) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = _ := by ring
  exact (abs_liuSelbergRemainder_le_fullDistributionMajorant _ N _ lam (by omega) hlam).trans
    ((liuPaperQSourceFullDistributionMajorant_le_coprime_add_r1 _ N _ (by omega) hε).trans
      ((add_le_add hcop hpaid).trans_eq (by unfold selbergRemainderConstant; ring)))


#print axioms numerical_selberg_remainder
end ChenEffective.GRH14
