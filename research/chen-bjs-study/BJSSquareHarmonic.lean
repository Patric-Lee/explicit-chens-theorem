import BJSPowerTails

/-! Pointwise estimates for the square-Moebius harmonic kernel. The
logarithmic tail is kept as log(n/sqrt(x)); log(x) is not bounded separately. -/
noncomputable section
namespace ChenEffective
open Real Finset
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def squareHarmonicResidual (x : ℝ) (n : ℕ) : ℝ :=
  (realHarmonic (x/(n:ℝ)^2)-(log x-2*log (n:ℝ)+eulerMascheroniConstant))/(n:ℝ)^2

theorem square_harmonic_head {x : ℝ} (hx : 1≤x) {n : ℕ}
    (hn : 1≤n) (hnx : (n:ℝ)≤sqrt x) :
    |squareHarmonicResidual x n| ≤ 2/x := by
  have hx0 : 0<x := by linarith only [hx]
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hn2 : (n:ℝ)^2≤x := (le_sqrt hn0.le hx0.le).mp hnx
  have hratio : 1≤x/(n:ℝ)^2 := (one_le_div (sq_pos_of_pos hn0)).mpr hn2
  have hh := real_harmonic_error_large hratio
  rw [log_div hx0.ne' (pow_ne_zero 2 hn0.ne'),log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  unfold squareHarmonicResidual
  rw [abs_div,abs_of_pos (sq_pos_of_pos hn0)]
  calc
    _ ≤ (2/(x/(n:ℝ)^2))/(n:ℝ)^2 :=
      div_le_div_of_nonneg_right (by simpa only [sub_sub] using hh) (sq_nonneg _)
    _ = _ := by field_simp

theorem square_harmonic_tail {x : ℝ} (hx : 1≤x) {q n : ℕ}
    (hq : 1≤q) (hqx : (q:ℝ)≤sqrt x) (hxn : sqrt x<(n:ℝ)) :
    |squareHarmonicResidual x n| ≤
      (4/sqrt q)*(1/((n:ℝ)*sqrt n))+1/(n:ℝ)^2 := by
  have hx0 : 0<x := by linarith only [hx]
  have hq0 : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
  have hn0 : (0:ℝ)<n := lt_trans (sqrt_pos.mpr hx0) hxn
  have hn2 : x<(n:ℝ)^2 := (sqrt_lt hx0.le hn0.le).mp hxn
  have hq2 : (q:ℝ)^2≤x := (le_sqrt hq0.le hx0.le).mp hqx
  have hsmall : x/(n:ℝ)^2<1 := (div_lt_one (sq_pos_of_pos hn0)).mpr hn2
  have hln : log x≤2*log (n:ℝ) := by
    have hh := log_le_log hx0 hn2.le
    simpa only [log_pow,Nat.cast_ofNat] using hh
  have hlq : 2*log (q:ℝ)≤log x := by
    have hh := log_le_log (sq_pos_of_pos hq0) hq2
    simpa only [log_pow,Nat.cast_ofNat] using hh
  have hrat : 0≤log ((n:ℝ)/q) := log_nonneg ((one_le_div hq0).mpr (hqx.trans hxn.le))
  have hlrat := log_div hn0.ne' hq0.ne'
  have hab : |-(log x-2*log (n:ℝ)+eulerMascheroniConstant)| ≤
      2*log ((n:ℝ)/q)+1 := by
    apply abs_le.mpr
    constructor <;> linarith only [hln,hlq,hrat,hlrat,
      one_half_lt_eulerMascheroniConstant,eulerMascheroniConstant_lt_two_thirds]
  have hlog := log_le_rpow_div (div_pos hn0 hq0).le (by norm_num : (0:ℝ)<1/2)
  rw [← sqrt_eq_rpow,sqrt_div hn0.le] at hlog
  have hsrq : 0<sqrt (q:ℝ) := sqrt_pos.mpr hq0
  have hsrn : 0<sqrt (n:ℝ) := sqrt_pos.mpr hn0
  have hsq := sq_sqrt hn0.le
  unfold squareHarmonicResidual
  rw [real_harmonic_zero_below_one hsmall,zero_sub,abs_div,abs_of_pos (sq_pos_of_pos hn0)]
  calc
    _ ≤ (2*log ((n:ℝ)/q)+1)/(n:ℝ)^2 :=
      div_le_div_of_nonneg_right hab (sq_nonneg _)
    _ ≤ (4*(sqrt n/sqrt q)+1)/(n:ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      linarith only [hlog]
    _ = _ := by field_simp; nlinarith only [hsq]

end ChenEffective
