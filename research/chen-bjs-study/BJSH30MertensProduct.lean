import BJSH30PrimeIntervals
import NumericalMertensProduct

noncomputable section
namespace ChenEffective.H30
open Real
open AnalyticNumberTheory.Mertens
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem sharp_mertens_product_log {n : ℕ} (hn : logPowerCutoff 2≤n) :
    |log (primeProduct n)+log (log (n:ℝ))+eulerMascheroniConstant|≤3/log (n:ℝ)^2 := by
  have hn9 : 9≤n := (logPowerCutoff_nine_le _).trans hn
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hl : 0<log (n:ℝ) := log_pos (by exact_mod_cast (show 1<n by omega))
  have hx : (3:ℝ)^120≤n := by
    have hp : (3:ℕ)^120≤logPowerCutoff 2 := by
      unfold logPowerCutoff
      exact Nat.pow_le_pow_right (by decide) (by norm_num)
    exact_mod_cast hp.trans hn
  have hm := dusart_sharp_mertens hx
  rw [Nat.floor_natCast] at hm
  have hc := logarithmicCorrection_tail_norm_le_div n (show 1≤n by omega)
  rw [Real.norm_eq_abs] at hc
  have hroot : sqrt (n:ℝ)≤(n:ℝ)/2 := sqrt_le_iff.mpr ⟨by positivity,by
    have h9 : (9:ℝ)≤n := by exact_mod_cast hn9
    nlinarith only [h9]⟩
  have hp : log (n:ℝ)^2≤(n:ℝ)/2 := (log_pow_le_sqrt_explicit hn).trans hroot
  have htail : 2/(n:ℝ)≤1/log (n:ℝ)^2 :=
    (div_le_div_iff₀ hnR (sq_pos_of_pos hl)).mpr (by linarith only [hp])
  rw [← mertensConstant_eq_eulerMascheroni,log_primeProduct_error_eq]
  have hh := abs_add_le (-(primeReciprocalSum n-(log (log (n:ℝ))+mertensSecondConstant)))
    (logarithmicCorrectionLimit-logarithmicCorrection n)
  rw [abs_neg] at hh
  have hm' : |primeReciprocalSum n-(log (log (n:ℝ))+mertensSecondConstant)|≤1/log (n:ℝ)^2 :=
    hm.trans (one_div_le_one_div_of_le (sq_pos_of_pos hl) (by nlinarith only [sq_nonneg (log (n:ℝ))]))
  have hh' := hh.trans (add_le_add hm' (hc.trans htail))
  have hi : (0:ℝ)≤1/log (n:ℝ)^2 := by positivity
  simp only [div_eq_mul_inv] at hh' hi ⊢
  linarith only [hh',hi]

def mertensProductThreshold (r : ℕ) : ℕ := max (logPowerCutoff 2) (3^(6*r+1))

theorem numerical_mertens_product {n r : ℕ} (hr : 0<r)
    (hn : mertensProductThreshold r≤n) :
    |primeProduct n*log (n:ℝ)*exp eulerMascheroniConstant-1|≤1/(r:ℝ) := by
  have hc : logPowerCutoff 2≤n := (le_max_left _ _).trans hn
  have hp : 3^(6*r+1)≤n := (le_max_right _ _).trans hn
  have hn9 : 9≤n := (logPowerCutoff_nine_le _).trans hc
  have hl : 0<log (n:ℝ) := log_pos (by exact_mod_cast (show 1<n by omega))
  have hrR : (1:ℝ)≤r := by exact_mod_cast hr
  have hL := log_ge_power_three hp
  norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hL
  have hpay : 6/log (n:ℝ)^2≤1/(r:ℝ) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hl) (by positivity : (0:ℝ)<r)).mpr
    nlinarith only [hL,hrR,sq_nonneg (log (n:ℝ)-1)]
  let E := log (primeProduct n)+log (log (n:ℝ))+eulerMascheroniConstant
  have he : |E|≤3/log (n:ℝ)^2 := sharp_mertens_product_log hc
  have he1 : |E|≤1 := by
    have hi : 1/(r:ℝ)≤1 := div_le_self (by norm_num) hrR
    have hh : 2*(3/log (n:ℝ)^2)≤1/(r:ℝ) := by
      calc
        _ = 6/log (n:ℝ)^2 := by ring
        _ ≤ _ := hpay
    linarith only [he,hh,hi,abs_nonneg E]
  have hb := (abs_exp_sub_one_le he1).trans (mul_le_mul_of_nonneg_left he (by norm_num))
  have hid : exp E=primeProduct n*log (n:ℝ)*exp eulerMascheroniConstant := by
    dsimp only [E]
    rw [exp_add,exp_add,exp_log (primeProduct_pos n),exp_log hl]
  rw [hid] at hb
  exact hb.trans (by
    calc
      _ = 6/log (n:ℝ)^2 := by ring
      _ ≤ _ := hpay)

#print axioms numerical_mertens_product
end ChenEffective.H30
