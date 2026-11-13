/- Threshold-specialized companion of research/chen-effective/NumericalSelbergRemainder.lean.
The original producer is retained; all modified numerical statements are rechecked. -/
import BJSH30PanR1

noncomputable section
namespace ChenEffective.H30
open MathlibNt.SieveTheory.LiuWeight
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def selbergRemainderConstant (A : ℕ) : ℝ :=
  panCanonicalConstant A+1920*liuLogarithmicIntegralUpperConstant 2
@[irreducible] def selbergRemainderThreshold (A m : ℕ) : ℕ :=
  max (panCanonicalThreshold A m) (logPowerCutoff (10*(A+6)))

theorem numerical_selberg_remainder (A m N : ℕ) (hm : 0 < m)
    (hN : selbergRemainderThreshold A m ≤ N) (lam : ℕ → ℝ)
    (hlam : LiuSelbergLambdaAdmissible N (1/(m : ℝ)) lam) :
    |liuSelbergRemainder (liuLogarithmicIntegral 2) N (1/(m : ℝ)) lam| ≤
      selbergRemainderConstant A*N/Real.log (N : ℝ)^A := by
  have hn := hN
  unfold selbergRemainderThreshold at hn
  obtain ⟨hNC, hNP⟩ := max_le_iff.mp hn
  have hN9 := (logPowerCutoff_nine_le _).trans hNP
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL := log_one_le_of_eight_le (by omega : 8 ≤ N)
  have hl0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL
  have hε : 0 ≤ 1/(m : ℝ) := by positivity
  have hcop := numerical_pan_canonical A m N hm hNC
  unfold LiuPaperQCoprimeRBound at hcop
  rw [Real.rpow_natCast] at hcop
  have hp := log_pow_le_rpow_inv_explicit (k := A+6) (m := 10)
    (by norm_num) (le_refl _) hNP
  norm_num only [Nat.cast_ofNat] at hp
  have hscale : (N : ℝ)^(9/10 : ℝ)*Real.log (N : ℝ)^6 ≤ N/Real.log (N : ℝ)^A := by
    apply (le_div_iff₀ (pow_pos hl0 A)).mpr
    calc
      _ = (N : ℝ)^(9/10 : ℝ)*Real.log (N : ℝ)^(A+6) := by rw [pow_add]; ring
      _ ≤ (N : ℝ)^(9/10 : ℝ)*(N : ℝ)^(1/10 : ℝ) := by gcongr
      _ = _ := by rw [← Real.rpow_add hN0]; norm_num
  have hr := numerical_pan_r1 2 N (1/(m : ℝ)) hN9 hε
  have hpaid : liuPaperQSourceR1Majorant (liuLogarithmicIntegral 2) N (1/(m : ℝ)) ≤
      1920*liuLogarithmicIntegralUpperConstant 2*N/Real.log (N : ℝ)^A := by
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
      _ ≤ (1920*liuLogarithmicIntegralUpperConstant 2)*(N/Real.log (N : ℝ)^A) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = _ := by ring
  exact (abs_liuSelbergRemainder_le_fullDistributionMajorant _ N _ lam (by omega) hlam).trans
    ((liuPaperQSourceFullDistributionMajorant_le_coprime_add_r1 _ N _ (by omega) hε).trans
      ((add_le_add hcop hpaid).trans_eq (by unfold selbergRemainderConstant; ring)))

#print axioms numerical_selberg_remainder
end ChenEffective.H30
