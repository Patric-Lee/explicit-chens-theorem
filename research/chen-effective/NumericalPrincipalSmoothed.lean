import NumericalPrincipalContour
import NumericalContourEdges
import NumericalResidueAssembly

namespace ChenEffective
open Set Function Filter Complex Real MeasureTheory
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem numerical_principal_smoothed_bound
    {T d ε X : ℝ} (hT : 1 ≤ T) (hd : 0 < d) (hd1 : d ≤ 1)
    (hε : 0 < ε) (hε1 : ε < 1) (hX : 1 ≤ X) :
    let χ : DirichletCharacter ℂ 1 := 1
    let J := 8192 * Real.log (32 * (T + 6) ^ 2) + 16
    ‖χ.twistedSmoothedPsi numericalSmoothing ε X -
      mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) 1 * X‖ ≤
      6144 * J * (T * X ^ (15 / 16 : ℝ) / ε + X ^ (1 + d) / (ε * (1 + T ^ 2))) +
      9216 * X ^ (1 + d) * (1 + d⁻¹ ^ 2) / (ε * T) := by
  let χ : DirichletCharacter ℂ 1 := 1
  let F := χ.twistedSmoothedPerronIntegrand numericalSmoothing ε X
  let J := 8192 * Real.log (32 * (T + 6) ^ 2) + 16
  have hJ : 0 ≤ J := by
    have hl : 0 ≤ Real.log (32 * (T + 6) ^ 2) := by
      apply Real.log_nonneg
      nlinarith [sq_nonneg (T - 1)]
    dsimp [J]
    linarith
  have hlog (σ t : ℝ) (hσ : (15 / 16 : ℝ) ≤ σ) (hσ2 : σ ≤ 2) (ht : |t| ≤ T)
      (he : σ = 15 / 16 ∨ |t| = T) :
      ‖deriv χ.LFunction (σ + t * I) / χ.LFunction (σ + t * I)‖ ≤ J := by
    rw [DirichletCharacter.LFunction_modOne_eq]
    apply numerical_principal_edge_log_bound hT (σ + t * I)
      (by simpa using hσ) (by simpa using hσ2) (by simpa using ht)
    simpa using he
  have hm : ∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) s‖ ≤
        768 * (ε * ‖s‖ ^ 2)⁻¹ :=
    fun s hs hs2 => numerical_smoothed_mellin_bound (1 / 2) (by norm_num) s hs hs2 ε hε hε1
  have hleft := numerical_perron_left χ hT hε hε1 hX hJ
    (fun t ht => hlog (15 / 16) t (le_refl _) (by norm_num) ht (Or.inl rfl))
  have htop := norm_twistedSmoothedPerron_horizontal_le_of_logDeriv_bound
    (by norm_num : (0 : ℝ) ≤ 768) hε hm χ (by norm_num : (1 / 2 : ℝ) ≤ 15 / 16)
    (by linarith : (15 / 16 : ℝ) ≤ 1 + d) (by linarith : 1 + d ≤ 2)
    hT (abs_of_nonneg (by linarith : 0 ≤ T)) hX hJ
    (fun σ hσ hσb => hlog σ T hσ (by linarith)
      (le_of_eq (abs_of_nonneg (by linarith))) (Or.inr (abs_of_nonneg (by linarith))))
  have hbottom := norm_twistedSmoothedPerron_horizontal_le_of_logDeriv_bound
    (by norm_num : (0 : ℝ) ≤ 768) hε hm χ (by norm_num : (1 / 2 : ℝ) ≤ 15 / 16)
    (by linarith : (15 / 16 : ℝ) ≤ 1 + d) (by linarith : 1 + d ≤ 2)
    hT (by rw [abs_neg, abs_of_nonneg (by linarith : 0 ≤ T)]) hX hJ
    (fun σ hσ hσb => hlog σ (-T) hσ (by linarith)
      (by rw [abs_neg, abs_of_nonneg (by linarith : 0 ≤ T)])
      (Or.inr (by rw [abs_neg, abs_of_nonneg (by linarith : 0 ≤ T)])))
  have ht := DirichletCharacter.twistedSmoothedPerron_right_tails_of_mellin_bound
    numericalSmoothing_contDiff (fun x _ => numericalSmoothing_nonneg x)
    numericalSmoothing_support numericalSmoothing_mass_one 768 (by norm_num)
    numerical_smoothed_mellin_bound χ hd hd1 hε hε1 (by positivity : 0 < X) hT
  have hf := DirichletCharacter.twistedSmoothedPerronIntegrand_integrable_right
    χ numericalSmoothing_contDiff (fun x _ => numericalSmoothing_nonneg x)
    numericalSmoothing_support numericalSmoothing_mass_one
    (by positivity : 0 < X) hε hε1 (by linarith : 1 < 1 + d) (by linarith : 1 + d ≤ 2)
  have hp := DirichletCharacter.twistedSmoothedPerron χ numericalSmoothing_contDiff
    (fun x _ => numericalSmoothing_nonneg x) numericalSmoothing_support numericalSmoothing_mass_one
    (by positivity : 0 < X) hε hε1 (σ := 1 + d) (by linarith) (by linarith)
  have hr : RectangleIntegral' F ((15 / 16 : ℂ) - I * T) ((1 + d : ℝ) + I * T) =
      mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) 1 * X := by
    change RectangleIntegral' (fun s => -deriv χ.LFunction s / χ.LFunction s *
      mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) s * (X : ℂ) ^ s) _ _ = _
    rw [DirichletCharacter.LFunction_modOne_eq]
    exact numerical_principal_rectangle (lt_of_lt_of_le zero_lt_one hT) hd hε hε1
      (lt_of_lt_of_le zero_lt_one hX)
  have hh := numerical_residue_assembly F
    (mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) 1 * X)
    (a := 15 / 16) (b := 1 + d) (T := T) (le_trans zero_le_one hT)
    hf (by simpa only [ofReal_div, ofReal_ofNat] using hr)
    hleft htop hbottom ht.1 ht.2
  change ‖χ.twistedSmoothedPsi numericalSmoothing ε X -
    mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) 1 * X‖ ≤ _
  rw [hp]
  convert hh using 1
  ring

#print axioms numerical_principal_smoothed_bound
end ChenEffective
