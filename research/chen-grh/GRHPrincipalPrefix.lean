import GRHPrincipal
import GRHPerronBudget
import NumericalMainTerm

/-! The numerical unsmoothed principal PNT input. The main term, removed
pole, smoothing error and contour error are all included explicitly. -/
namespace ChenEffective.GRH
open Set Function Filter Complex Real MeasureTheory
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

theorem principal_prefix_numerical {X : ℝ} (hX : 1 ≤ X)
    (hL : (10:ℝ) ≤ Real.log X) :
    ‖lambdaCharacterPrefix ⌊X⌋₊ 1 (1 : DirichletCharacter ℂ 1)-(X:ℂ)‖ ≤
      (10^14:ℝ)*(Real.log X)^2*X^(501/1000:ℝ) := by
  let L := Real.log X
  let d := 1/L
  let ε := 1/Real.sqrt X
  let J := (64000000:ℝ)*Real.log (32*(X+6)^2)+4
  let χ : DirichletCharacter ℂ 1 := 1
  let S := χ.twistedSmoothedPsi numericalSmoothing ε X
  let R : ℂ := mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) 1*X
  have hX0 : 0 < X := by linarith only [hX]
  have hX11 : 11 ≤ X := by linarith only [Real.log_le_sub_one_of_pos hX0,hL]
  have hL0 : 0 < L := by dsimp only [L]; linarith only [hL]
  have hs0 : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hs2 : 2 < Real.sqrt X := (Real.lt_sqrt (by norm_num)).mpr (by linarith only [hX11])
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hε1 : ε < 1 := by dsimp only [ε]; exact (div_lt_one hs0).mpr (by linarith only [hs2])
  have hεX : ε*X = Real.sqrt X := by
    dsimp only [ε]
    field_simp [hs0.ne']
    nlinarith only [Real.sq_sqrt hX0.le]
  have hd : 0 < d := by dsimp only [d]; positivity
  have hd1 : d ≤ 1 := by
    dsimp only [d]
    exact (div_le_one hL0).mpr (by dsimp only [L]; linarith only [hL])
  have hlog2 : Real.log (2:ℝ) ≤ 1 := by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hlog : Real.log (32*(X+6)^2) ≤ 3*L := by
    have hh := Real.log_le_log (by linarith only [hX0] : (0:ℝ)<X+6)
      (show X+6 ≤ 2*X by linarith only [hX11])
    rw [Real.log_mul (by norm_num) hX0.ne'] at hh
    rw [Real.log_mul (by norm_num) (by positivity : ((X+6)^2:ℝ) ≠ 0),
      Real.log_pow,show (32:ℝ)=2^5 by norm_num,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    dsimp only [L]
    linarith only [hh,hlog2,hL]
  have hJ : J ≤ (1000000000:ℝ)*L := by
    dsimp only [J]
    nlinarith only [hlog,hL]
  have hJ0 : 0 ≤ J := by
    have hh : 0 ≤ Real.log (32*(X+6)^2) := by
      apply Real.log_nonneg
      nlinarith only [hX,sq_nonneg (X-1)]
    dsimp only [J]
    positivity
  have hsm := principal_smoothed_bound (a := 1/1000) (T := X) (d := d) (ε := ε)
    (by norm_num) (by norm_num) hX hd hd1 hε hε1 hX
  norm_num only [show (1/2+1/1000:ℝ)=501/1000 by norm_num,
    show (64/(1/1000:ℝ)^2) = 64000000 by norm_num] at hsm
  have hr := numerical_smoothing_removal numericalSmoothing_contDiff numericalSmoothing_support
    (fun x _ => numericalSmoothing_nonneg x) numericalSmoothing_mass_one χ X
    (by linarith only [hX11]) ε hε hε1 (by rw [mul_comm,hεX]; exact hs2)
  have hm : ‖R-(X:ℂ)‖ ≤ 2*ε*X := by
    have hh := numerical_mellin_main_term hε hε1
    have he : R-(X:ℂ) =
        (mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) 1-1)*X := by dsimp only [R]; ring
    rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hX0]
    exact mul_le_mul_of_nonneg_right hh hX0.le
  have htri : ‖lambdaCharacterPrefix ⌊X⌋₊ 1 χ-(X:ℂ)‖ ≤
      ‖lambdaCharacterPrefix ⌊X⌋₊ 1 χ-S‖+‖S-R‖+‖R-(X:ℂ)‖ := by
    calc
      _ = ‖(lambdaCharacterPrefix ⌊X⌋₊ 1 χ-S)+(S-R)+(R-(X:ℂ))‖ := by congr 1; ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  rw [norm_sub_rev] at hr
  have hp := perron_envelope_payment hX hL (A := L) le_rfl hJ hJ0
  apply le_trans _ hp
  have hpay : 60*ε*X*Real.log X+2*ε*X ≤ 62*ε*X*Real.log X := by
    have hh := mul_nonneg (show 0 ≤ ε*X by positivity)
      (show 0 ≤ Real.log X-1 by linarith only [hL])
    nlinarith only [hh]
  nlinarith only [htri,hsm,hr,hm,hpay]

#print axioms principal_prefix_numerical
end ChenEffective.GRH
