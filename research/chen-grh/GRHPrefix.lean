import GRHSharpPerron

/-! An unsmoothed, fully numerical character-prefix estimate. It applies to
all nonprincipal characters, including imprimitive ones. The conductor and
range dependence are explicit. This is an input for AP aggregation, not
an asserted Chen lower-count estimate. -/
namespace ChenEffective.GRH
open Set Function Filter Complex Real MeasureTheory
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

theorem nonprincipal_prefix_numerical {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {X : ℝ}
    (hX : 1 ≤ X) (hL : (10:ℝ) ≤ Real.log X) :
    ‖lambdaCharacterPrefix ⌊X⌋₊ q χ‖ ≤
      (10^13:ℝ)*(Real.log q+Real.log X)^2*X^(501/1000:ℝ) := by
  let L := Real.log X
  let A := Real.log (q:ℝ)+L
  let d := 1/L
  let ε := 1/Real.sqrt X
  let J := (64000000:ℝ)*Real.log (16*(q:ℝ)*(X+4))
  let Y := X^(501/1000:ℝ)
  have hX0 : 0 < X := by linarith only [hX]
  have hX11 : 11 ≤ X := by linarith only [Real.log_le_sub_one_of_pos hX0,hL]
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (0:ℝ) < q := by linarith only [hq]
  have hlq : 0 ≤ Real.log (q:ℝ) := Real.log_nonneg hq
  have hL0 : 0 < L := by dsimp only [L]; linarith only [hL]
  have hA : 10 ≤ A := by dsimp only [A,L]; linarith only [hL,hlq]
  have hA0 : 0 ≤ A := by linarith only [hA]
  have hLA : L ≤ A := by dsimp only [A]; linarith only [hlq]
  have hs0 : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hs2 : 2 < Real.sqrt X := by
    apply (Real.lt_sqrt (by norm_num)).mpr
    linarith only [hX11]
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hε1 : ε < 1 := by dsimp only [ε]; exact (div_lt_one hs0).mpr (by linarith only [hs2])
  have hεX : ε*X = Real.sqrt X := by
    dsimp only [ε]
    field_simp [hs0.ne']
    nlinarith only [Real.sq_sqrt hX0.le]
  have hεX2 : 2 < X*ε := by rw [mul_comm,hεX]; exact hs2
  have hd : 0 < d := by dsimp only [d]; positivity
  have hd1 : d ≤ 1 := by
    dsimp only [d]
    exact (div_le_one hL0).mpr (by dsimp only [L]; linarith only [hL])
  have hdi : d⁻¹ = L := by simp [d,one_div]
  have hY : Real.sqrt X ≤ Y := by
    dsimp only [Y]
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
  have hY1 : 1 ≤ Y := (by linarith only [hs2] : (1:ℝ) ≤ Real.sqrt X).trans hY
  have hY0 : 0 ≤ Y := by linarith only [hY1]
  have hAY : 1 ≤ A*Y := by nlinarith only [hA,hY1]
  have hpow : X^(1+d) ≤ 3*X := by
    have hh : X^d = Real.exp 1 := by
      rw [Real.rpow_def_of_pos hX0]
      congr 1
      dsimp only [d,L]
      field_simp [show Real.log X ≠ 0 from hL0.ne']
    rw [Real.rpow_add hX0,Real.rpow_one,hh]
    have he : Real.exp 1 ≤ 3 := by linarith only [Real.exp_one_lt_d9]
    nlinarith only [mul_le_mul_of_nonneg_left he hX0.le]
  have hlog2 : Real.log (2:ℝ) ≤ 1 := by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hlogT : Real.log (1+X) ≤ 2*L := by
    have hh := Real.log_le_log (by linarith only [hX0] : (0:ℝ)<1+X)
      (show 1+X ≤ 2*X by linarith only [hX])
    rw [Real.log_mul (by norm_num) hX0.ne'] at hh
    dsimp only [L]
    linarith only [hh,hlog2,hL]
  have hlogT0 : 0 ≤ Real.log (1+X) := Real.log_nonneg (by linarith only [hX0])
  have hJ : J ≤ (128000000:ℝ)*A := by
    have hb : 16*(q:ℝ)*(X+4) ≤ 32*(q:ℝ)*X := by nlinarith only [hq0,hX11]
    have hh := Real.log_le_log (by positivity : (0:ℝ)<16*(q:ℝ)*(X+4)) hb
    rw [Real.log_mul (by positivity : (32*(q:ℝ)) ≠ 0) hX0.ne',
      Real.log_mul (by norm_num) hq0.ne',
      show (32:ℝ)=2^5 by norm_num,Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    dsimp only [J,A,L]
    linarith only [hh,hlog2,hL,hlq]
  have hJ0 : 0 ≤ J := by
    dsimp only [J]
    apply mul_nonneg (by norm_num)
    apply Real.log_nonneg
    nlinarith only [hq,hX11]
  have hD : X ≤ ε*(1+X^2) := by
    have hh : ε*X^2 = Real.sqrt X*X := by rw [pow_two,← mul_assoc,hεX]
    nlinarith only [hh,mul_le_mul_of_nonneg_right (by linarith only [hs2] : (1:ℝ)≤Real.sqrt X) hX0.le,hε]
  have hfrac : X^(1+d)/(ε*(1+X^2)) ≤ 3 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [hpow,hD]
  have hinner : 4608*Y*Real.log (1+X)+6144*X^(1+d)/(ε*(1+X^2)) ≤ 30000*A*Y := by
    have hv : 4608*Y*Real.log (1+X) ≤ 9216*A*Y := by
      have hh := mul_le_mul_of_nonneg_left hlogT (show 0 ≤ 4608*Y by positivity)
      have hh2 := mul_le_mul_of_nonneg_right hLA (show 0 ≤ 9216*Y by positivity)
      nlinarith only [hh,hh2]
    have hh := mul_le_mul_of_nonneg_left hfrac (by norm_num : (0:ℝ) ≤ 6144)
    have hid : 6144*X^(1+d)/(ε*(1+X^2)) = 6144*(X^(1+d)/(ε*(1+X^2))) := by ring
    rw [← hid] at hh
    nlinarith only [hv,hh,hAY]
  have hmain : J*(4608*Y*Real.log (1+X)+6144*X^(1+d)/(ε*(1+X^2))) ≤
      (3840000000000:ℝ)*A^2*Y := by
    calc
      _ ≤ ((128000000:ℝ)*A)*(30000*A*Y) :=
        mul_le_mul hJ hinner (by positivity) (by positivity)
      _ = _ := by ring
  have htail : 9216*X^(1+d)*(1+d⁻¹^2)/(ε*X) ≤ 60000*A^2*Y := by
    rw [hdi,hεX]
    have hr : X/Real.sqrt X = Real.sqrt X := by
      apply (div_eq_iff hs0.ne').mpr
      nlinarith only [Real.sq_sqrt hX0.le]
    calc
      _ ≤ 9216*(3*X)*(1+L^2)/Real.sqrt X := by gcongr
      _ = 27648*(X/Real.sqrt X)*(1+L^2) := by ring
      _ = 27648*Real.sqrt X*(1+L^2) := by rw [hr]
      _ ≤ 27648*Y*(2*A^2) := by
        gcongr
        nlinarith only [hLA,hA,hL,pow_le_pow_left₀ (by linarith only [hL] : (0:ℝ)≤L) hLA 2]
      _ ≤ _ := by nlinarith only [sq_nonneg A,show 0 ≤ A^2*Y by positivity]
  have hsm := smoothed_perron_bound χ hχ (a := 1/1000) (T := X) (d := d) (ε := ε)
    (by norm_num) (by norm_num) hX hd hd1 hε hε1 hX
  norm_num only [show (1/2+1/1000:ℝ)=501/1000 by norm_num,
    show (64/(1/1000:ℝ)^2) = 64000000 by norm_num] at hsm
  have hr := numerical_smoothing_removal numericalSmoothing_contDiff numericalSmoothing_support
    (fun x _ => numericalSmoothing_nonneg x) numericalSmoothing_mass_one χ X
    (by linarith only [hX11]) ε hε hε1 hεX2
  have hrem : 60*ε*X*Real.log X ≤ 60*A^2*Y := by
    rw [mul_assoc 60 ε X,hεX]
    change 60*Real.sqrt X*L ≤ _
    have hLAA : L ≤ A^2 := by nlinarith only [hLA,hA]
    have hh := mul_le_mul hY hLAA (by dsimp only [L]; linarith only [hL]) (by positivity : (0:ℝ)≤Y)
    nlinarith only [hh]
  have htri : ‖lambdaCharacterPrefix ⌊X⌋₊ q χ‖ ≤
      ‖χ.twistedSmoothedPsi numericalSmoothing ε X‖+
      ‖χ.twistedSmoothedPsi numericalSmoothing ε X-lambdaCharacterPrefix ⌊X⌋₊ q χ‖ := by
    calc
      _ = ‖χ.twistedSmoothedPsi numericalSmoothing ε X-
          (χ.twistedSmoothedPsi numericalSmoothing ε X-lambdaCharacterPrefix ⌊X⌋₊ q χ)‖ := by congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  change _ ≤ (10^13:ℝ)*A^2*Y
  have hsm' : ‖χ.twistedSmoothedPsi numericalSmoothing ε X‖ ≤
      (3840000000000:ℝ)*A^2*Y+60000*A^2*Y :=
    hsm.trans (add_le_add hmain htail)
  nlinarith only [htri,hsm',hr.trans hrem,show 0 ≤ A^2*Y by positivity]

#print axioms nonprincipal_prefix_numerical
end ChenEffective.GRH
