import NumericalPrimitiveContour
import ExplicitLogBounds

namespace ChenEffective
open Complex Real Set
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- Fully specified contour parameters: no selected constants or eventual cutoffs. -/
theorem numerical_primitive_prefix_power_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {X : ℝ} (hX : 9 ≤ X) :
    ‖lambdaCharacterPrefix ⌊X⌋₊ q χ‖ ≤
      (10000000000 + 200000000 * Real.log (16 * (q : ℝ) * (X ^ (1 / 32 : ℝ) + 4)) +
        60 * Real.log X) * X ^ (127 / 128 : ℝ) := by
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  let T := X ^ (1 / 32 : ℝ)
  let ε := X ^ (-1 / 128 : ℝ)
  let P := X ^ (127 / 128 : ℝ)
  let L := Real.log (16 * (q : ℝ) * (T + 4))
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
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hL : 0 ≤ L := by apply Real.log_nonneg; nlinarith only [hq, hT]
  have ha : T * X ^ (15 / 16 : ℝ) / ε ≤ P := by
    dsimp [T, ε, P]
    rw [div_eq_mul_inv, ← Real.rpow_neg hX0.le, ← Real.rpow_add hX0, ← Real.rpow_add hX0]
    apply Real.rpow_le_rpow_of_exponent_le hX1
    norm_num
  have hb : X ^ (1 + (1 / 1024 : ℝ)) / (ε * (1 + T ^ 2)) ≤ P := by
    calc
      _ ≤ X ^ (1 + (1 / 1024 : ℝ)) / (ε * T ^ 2) := by gcongr; linarith [sq_nonneg T]
      _ = X ^ (969 / 1024 : ℝ) := by
        dsimp [T, ε]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0,
          ← Real.rpow_sub hX0]
        norm_num
      _ ≤ P := Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  have hc : X ^ (1 + (1 / 1024 : ℝ)) / (ε * T) ≤ P := by
    calc
      _ = X ^ (1001 / 1024 : ℝ) := by
        dsimp [T, ε]
        rw [← Real.rpow_add hX0, ← Real.rpow_sub hX0]
        norm_num
      _ ≤ P := Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  have hs := numerical_primitive_smoothed_bound χ hχ hT
    (by norm_num : (0 : ℝ) < 1 / 1024) (by norm_num : (1 / 1024 : ℝ) ≤ 1)
    hε hε1 hX1
  have hr := numerical_smoothing_removal numericalSmoothing_contDiff numericalSmoothing_support
    (fun x _ => numericalSmoothing_nonneg x) numericalSmoothing_mass_one χ X (by linarith)
    ε hε hε1 (by rw [hprod]; exact hP)
  have hr' : ‖χ.twistedSmoothedPsi numericalSmoothing ε X - lambdaCharacterPrefix ⌊X⌋₊ q χ‖ ≤
      60 * Real.log X * P := hr.trans (by rw [show 60 * ε * X * Real.log X =
        60 * Real.log X * (X * ε) by ring, hprod])
  have hs' : ‖χ.twistedSmoothedPsi numericalSmoothing ε X‖ ≤
      (10000000000 + 200000000 * L) * P := by
    apply hs.trans
    change 50331648 * L * (_ + _) + _ ≤ _
    have hp0 : 0 ≤ P := by positivity
    have hcp : 9216 * X ^ (1 + (1 / 1024 : ℝ)) * (1 + (1 / 1024 : ℝ)⁻¹ ^ 2) /
        (ε * T) ≤ 9663685632 * P := by
      calc
        _ = 9663685632 * (X ^ (1 + (1 / 1024 : ℝ)) / (ε * T)) := by norm_num; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hc (by norm_num)
    have hab := mul_le_mul_of_nonneg_left (add_le_add ha hb)
      (show 0 ≤ 50331648 * L by positivity)
    nlinarith only [hab, hcp, hL, hp0, mul_nonneg hL hp0]
  have hn := norm_sub_le (χ.twistedSmoothedPsi numericalSmoothing ε X)
    (χ.twistedSmoothedPsi numericalSmoothing ε X - lambdaCharacterPrefix ⌊X⌋₊ q χ)
  rw [sub_sub_cancel] at hn
  exact hn.trans ((add_le_add hs' hr').trans (by dsimp [L, P, T]; ring_nf; rfl))

#print axioms numerical_primitive_prefix_power_bound
end ChenEffective
