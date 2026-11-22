import BJSH30MertensProduct

noncomputable section
namespace ChenEffective.GRH1337
open Real
open AnalyticNumberTheory.Mertens
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def mertensProductThreshold (r : ℕ) : ℕ := max (logPowerCutoff 2) (3^(Nat.sqrt (6*r)+2))

theorem numerical_mertens_product {n r : ℕ} (hr : 0<r)
    (hn : mertensProductThreshold r≤n) :
    |primeProduct n*log (n:ℝ)*exp eulerMascheroniConstant-1|≤1/(r:ℝ) := by
  have hc : logPowerCutoff 2≤n := (le_max_left _ _).trans hn
  have hp : 3^(Nat.sqrt (6*r)+2)≤n := (le_max_right _ _).trans hn
  have hn9 : 9≤n := (logPowerCutoff_nine_le _).trans hc
  have hl : 0<log (n:ℝ) := log_pos (by exact_mod_cast (show 1<n by omega))
  have hrR : (1:ℝ)≤r := by exact_mod_cast hr
  have hL := log_ge_power_three hp
  norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hL
  have hpay : 6/log (n:ℝ)^2≤1/(r:ℝ) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hl) (by positivity : (0:ℝ)<r)).mpr
    have hs := Nat.lt_succ_sqrt' (6*r)
    have hsR : (6:ℝ)*r < ((Nat.sqrt (6*r):ℝ)+1)^2 := by exact_mod_cast hs
    have ht : ((Nat.sqrt (6*r):ℝ)+1)^2 ≤ log (n:ℝ)^2 := by
      apply pow_le_pow_left₀ (by positivity)
      linarith only [hL]
    linarith only [hsR,ht]
  let E := log (primeProduct n)+log (log (n:ℝ))+eulerMascheroniConstant
  have he : |E|≤3/log (n:ℝ)^2 := H30.sharp_mertens_product_log hc
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
end ChenEffective.GRH1337
