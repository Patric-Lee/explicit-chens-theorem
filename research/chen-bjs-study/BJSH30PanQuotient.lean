/- Threshold-specialized companion of research/chen-effective/NumericalPanQuotient.lean.
The original producer is retained; all modified numerical statements are rechecked. -/
import NumericalBV
import MathlibNt.AnalyticNumberTheory.LargeSieve.PanQuotientBounds

namespace ChenEffective.H30
open Real
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem numerical_nat_div_quarter {N : ℕ} (hN : 4096 ≤ N)
    (a : ℕ) (ha : 1 ≤ a) (haN : (a : ℝ) ≤ (N : ℝ)^(2/3 : ℝ)) :
    (N : ℝ)^(1/4 : ℝ) ≤ (N/a : ℕ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := by positivity
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hG : (2 : ℝ) ≤ (N : ℝ)^(1/12 : ℝ) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num : (0 : ℝ) ≤ 2) hN0.le
      (by norm_num : (0 : ℝ) < 12)).mpr
    norm_num
    exact_mod_cast hN
  have hquarter : 1 ≤ (N : ℝ)^(1/4 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  have hsplit : (N : ℝ)^(1/4 : ℝ) * (N : ℝ)^(1/12 : ℝ) = (N : ℝ)^(1/3 : ℝ) := by
    rw [← Real.rpow_add hN0]; norm_num
  have hgap : (N : ℝ)^(1/4 : ℝ)+1 ≤ (N : ℝ)^(1/3 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hG (Real.rpow_nonneg hN0.le (1/4 : ℝ))
    rw [hsplit] at hh
    linarith only [hh, hquarter]
  have hprod : (N : ℝ)^(1/3 : ℝ) * (a : ℝ) ≤ N := by
    calc
      _ ≤ (N : ℝ)^(1/3 : ℝ) * (N : ℝ)^(2/3 : ℝ) :=
        mul_le_mul_of_nonneg_left haN (by positivity)
      _ = _ := by rw [← Real.rpow_add hN0]; norm_num
  have hfloor : (N : ℝ) < (N/a : ℕ)*(a : ℝ)+a := by
    exact_mod_cast (Nat.lt_div_mul_add (show 0 < a by omega) : N < N/a*a+a)
  have hlt : (N : ℝ)^(1/3 : ℝ) < (N/a : ℕ)+1 := by nlinarith only [hprod, hfloor, ha0]
  linarith only [hgap, hlt]

@[irreducible] def panQuotientThreshold (b M : ℕ) : ℕ :=
  max 4096 (max (M^4) (3^(4*2^b+1)))

theorem numerical_quotient_parameters (b M N : ℕ) (hN : panQuotientThreshold b M ≤ N)
    (a : ℕ) (ha : 1 ≤ a) (haN : (a : ℝ) ≤ (N : ℝ)^(2/3 : ℝ)) :
    M ≤ N/a ∧ 0 < Real.log (N : ℝ) ∧ 0 < Real.log (N/a : ℕ) ∧
      Real.log (N : ℝ) ≤ 4*Real.log (N/a : ℕ) ∧
      (4 : ℝ)^b ≤ Real.log (N/a : ℕ)^2 := by
  have hn := hN
  unfold panQuotientThreshold at hn
  have hN4096 : 4096 ≤ N := (le_max_left _ _).trans hn
  have hM4 : M^4 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hlog := log_ge_power_three
    ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  push_cast at hlog
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hquarter := numerical_nat_div_quarter hN4096 a ha haN
  have hMpow : (M : ℝ) ≤ (N : ℝ)^(1/4 : ℝ) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg M) hN0.le
      (by norm_num : (0 : ℝ) < 4)).mpr
    norm_num only [Real.rpow_ofNat]
    exact_mod_cast hM4
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hc := Real.log_le_log (Real.rpow_pos_of_pos hN0 (1/4 : ℝ)) hquarter
  rw [Real.log_rpow hN0] at hc
  have hlogt : 0 < Real.log (N/a : ℕ) := by linarith only [hc, hlogpos]
  refine ⟨by exact_mod_cast hMpow.trans hquarter, hlogpos, hlogt, ?_, ?_⟩
  · linarith only [hc]
  · have hhalf : (2:ℝ)^b≤Real.log (N/a:ℕ) := by linarith only [hc,hlog]
    have hs := pow_le_pow_left₀ (by positivity : (0:ℝ)≤2^b) hhalf 2
    have he : ((2:ℝ)^b)^2=(4:ℝ)^b := by rw [← pow_mul,mul_comm b 2,pow_mul]; norm_num
    rwa [he] at hs

#print axioms numerical_quotient_parameters
end ChenEffective.H30
