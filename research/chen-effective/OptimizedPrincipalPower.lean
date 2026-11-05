import NumericalPrincipalSmoothed
import NumericalMainTerm
import ExplicitLogBounds

namespace ChenEffective
open Complex Real Set
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem optimized_principal_prefix_power_bound {X : ℝ} (hX : 9 ≤ X) :
    ‖lambdaCharacterPrefix ⌊X⌋₊ 1 (1 : DirichletCharacter ℂ 1) - (X : ℂ)‖ ≤
      (30000000000 + 200000000 * Real.log (32 * (X ^ (1 / 32 : ℝ) + 6) ^ 2) +
        60 * Real.log X) * X ^ (67 / 68 : ℝ) := by
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  let T := X ^ (1 / 32 : ℝ)
  let ε := X ^ (-1 / 68 : ℝ)
  let P := X ^ (67 / 68 : ℝ)
  let L := Real.log (32 * (T + 6) ^ 2)
  have hT : 1 ≤ T := Real.one_le_rpow hX1 (by norm_num)
  have hT0 : 0 < T := by positivity
  have hε : 0 < ε := by positivity
  have hε1 : ε < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
  have hprod : X * ε = P := by
    dsimp [ε, P]
    nth_rw 1 [← Real.rpow_one X]
    rw [← Real.rpow_add hX0]
    norm_num
  have hP : 2 < P := by
    have hh : Real.sqrt X ≤ P := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
    have hh2 : (3 : ℝ) ≤ Real.sqrt X := (Real.le_sqrt (by norm_num) hX0.le).mpr (by linarith)
    linarith
  have hL : 0 ≤ L := by apply Real.log_nonneg; nlinarith only [hT, sq_nonneg (T - 1)]
  have ha : T * X ^ (15 / 16 : ℝ) / ε ≤ P := by
    dsimp [T, ε, P]
    rw [div_eq_mul_inv, ← Real.rpow_neg hX0.le, ← Real.rpow_add hX0, ← Real.rpow_add hX0]
    apply Real.rpow_le_rpow_of_exponent_le hX1
    norm_num
  have hb : X ^ (1 + (1 / 1024 : ℝ)) / (ε * (1 + T ^ 2)) ≤ P := by
    calc
      _ ≤ X ^ (1 + (1 / 1024 : ℝ)) / (ε * T ^ 2) := by gcongr; linarith [sq_nonneg T]
      _ = X ^ (16593 / 17408 : ℝ) := by
        dsimp [T, ε]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0,
          ← Real.rpow_sub hX0]
        norm_num
      _ ≤ P := Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)

  have hc : X ^ (1 + (1 / 1024 : ℝ)) / (ε * T) ≤ P := by
    calc
      _ = X ^ (17137 / 17408 : ℝ) := by
        dsimp [T, ε]
        rw [← Real.rpow_add hX0, ← Real.rpow_sub hX0]
        norm_num
      _ ≤ P := Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  let χ : DirichletCharacter ℂ 1 := 1
  let S := χ.twistedSmoothedPsi numericalSmoothing ε X
  let A : ℂ := mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) 1 * X
  have hs := numerical_principal_smoothed_bound hT
    (by norm_num : (0 : ℝ) < 1 / 1024) (by norm_num : (1 / 1024 : ℝ) ≤ 1)
    hε hε1 hX1
  have hr := numerical_smoothing_removal numericalSmoothing_contDiff numericalSmoothing_support
    (fun x _ => numericalSmoothing_nonneg x) numericalSmoothing_mass_one χ X (by linarith)
    ε hε hε1 (by rw [hprod]; exact hP)
  have hr' : ‖lambdaCharacterPrefix ⌊X⌋₊ 1 χ - S‖ ≤ 60 * Real.log X * P := by
    rw [norm_sub_rev]
    exact hr.trans (by rw [show 60 * ε * X * Real.log X =
      60 * Real.log X * (X * ε) by ring, hprod])
  have hm : ‖A - (X : ℂ)‖ ≤ 2 * P := by
    have hh := numerical_mellin_main_term hε hε1
    have he : A - (X : ℂ) =
        (mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) 1 - 1) * X := by
      dsimp [A]
      ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX0]
    have hp := mul_le_mul_of_nonneg_right hh hX0.le
    exact hp.trans (by rw [show 2 * ε * X = 2 * (X * ε) by ring, hprod])
  have hs' : ‖S - A‖ ≤ (20000000000 + 200000000 * L) * P := by
    apply hs.trans
    change 6144 * (8192 * L + 16) * (_ + _) + _ ≤ _
    have hp0 : 0 ≤ P := by positivity
    have hcp : 9216 * X ^ (1 + (1 / 1024 : ℝ)) * (1 + (1 / 1024 : ℝ)⁻¹ ^ 2) /
        (ε * T) ≤ 9663685632 * P := by
      calc
        _ = 9663685632 * (X ^ (1 + (1 / 1024 : ℝ)) / (ε * T)) := by norm_num; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hc (by norm_num)
    have hab := mul_le_mul_of_nonneg_left (add_le_add ha hb)
      (show 0 ≤ 6144 * (8192 * L + 16) by positivity)
    nlinarith only [hab, hcp, hL, hp0, mul_nonneg hL hp0]
  calc
    _ = ‖(lambdaCharacterPrefix ⌊X⌋₊ 1 χ - S) + (S - A) + (A - (X : ℂ))‖ := by
      congr 1
      ring
    _ ≤ ‖lambdaCharacterPrefix ⌊X⌋₊ 1 χ - S‖ + ‖S - A‖ + ‖A - (X : ℂ)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ 60 * Real.log X * P + (20000000000 + 200000000 * L) * P + 2 * P :=
      add_le_add (add_le_add hr' hs') hm
    _ ≤ _ := by dsimp [L, T, P]; nlinarith [Real.rpow_nonneg hX0.le (67 / 68 : ℝ)]

#print axioms optimized_principal_prefix_power_bound
end ChenEffective
