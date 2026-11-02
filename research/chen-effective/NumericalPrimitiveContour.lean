import NumericalDirichletStrip
import NumericalRightTail
import MathlibNt.AnalyticNumberTheory.LargeSieve.DirichLTwistedSmoothedNonquadraticErrorAssembly

namespace ChenEffective
open Set Function Filter Complex Real MeasureTheory
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem numerical_primitive_finite_shift {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {T d ε X : ℝ} (_hT : 1 ≤ T) (hd : 0 < d) (_hd1 : d ≤ 1)
    (hε : 0 < ε) (hε1 : ε < 1) (hX : 0 < X) :
    let F := DirichletCharacter.twistedSmoothedPerronIntegrand χ numericalSmoothing ε X
    VIntegral F (1 + d) (-T) T - VIntegral F (15 / 16) (-T) T =
      HIntegral F (15 / 16) (1 + d) T - HIntegral F (15 / 16) (1 + d) (-T) := by
  let F := DirichletCharacter.twistedSmoothedPerronIntegrand χ numericalSmoothing ε X
  let z : ℂ := 15 / 16 - I * T
  let w : ℂ := (1 + d : ℝ) + I * T
  have hRe : ∀ s ∈ z.Rectangle w, (15 / 16 : ℝ) ≤ s.re := by
    intro s hs
    rw [Complex.Rectangle, Complex.mem_reProdIm] at hs
    norm_num [z, w] at hs
    rw [uIcc_of_le (by linarith : (15 / 16 : ℝ) ≤ 1 + d)] at hs
    exact hs.1.1
  have hL : Differentiable ℂ χ.LFunction := χ.differentiable_LFunction hχ
  have hlog : HolomorphicOn (fun s => -deriv χ.LFunction s / χ.LFunction s) (z.Rectangle w) :=
    hL.deriv.differentiableOn.neg.div hL.differentiableOn (by
      intro s hs
      exact dirichlet_seven_eighths χ (by linarith [hRe s hs]) (by tauto))
  have hh : HolomorphicOn F (z.Rectangle w) := by
    apply DifferentiableOn.mul
    · apply DifferentiableOn.mul hlog
      intro s hs
      exact (Smooth1MellinDifferentiable numericalSmoothing_contDiff numericalSmoothing_support
        ⟨hε, hε1⟩ (fun x _ => numericalSmoothing_nonneg x) numericalSmoothing_mass_one
        (by linarith [hRe s hs])).differentiableWithinAt
    · intro s _
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.const_cpow (by fun_prop)
      left
      exact_mod_cast hX.ne'
  have hz := hh.vanishesOnRectangle (by rfl)
  norm_num [RectangleIntegral, z, w] at hz
  change VIntegral F (1 + d) (-T) T - VIntegral F (15 / 16) (-T) T = _
  linear_combination hz

theorem numerical_primitive_smoothed_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {T d ε X : ℝ} (hT : 1 ≤ T) (hd : 0 < d) (hd1 : d ≤ 1)
    (hε : 0 < ε) (hε1 : ε < 1) (hX : 1 ≤ X) :
    ‖χ.twistedSmoothedPsi numericalSmoothing ε X‖ ≤
      50331648 * Real.log (16 * (q : ℝ) * (T + 4)) *
        (T * X ^ (15 / 16 : ℝ) / ε + X ^ (1 + d) / (ε * (1 + T ^ 2))) +
      9216 * X ^ (1 + d) * (1 + d⁻¹ ^ 2) / (ε * T) := by
  let F := DirichletCharacter.twistedSmoothedPerronIntegrand χ numericalSmoothing ε X
  let J := 8192 * Real.log (16 * (q : ℝ) * (T + 4))
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hJ : 0 ≤ J := by
    apply mul_nonneg (by norm_num)
    apply Real.log_nonneg
    nlinarith only [hq, hT]
  have hlog (σ t : ℝ) (hσ : (15 / 16 : ℝ) ≤ σ) (hσ2 : σ ≤ 2) (ht : |t| ≤ T) :
      ‖deriv χ.LFunction (σ + t * I) / χ.LFunction (σ + t * I)‖ ≤ J := by
    have hh := numerical_dirichlet_logDerivative_strip χ hχ (σ + t * I)
      (by simpa using hσ) (by simpa using hσ2)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, zero_mul,
      add_zero, mul_one, zero_add] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by positivity) (by gcongr)) (by norm_num))
  have hm : ∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) s‖ ≤
        768 * (ε * ‖s‖ ^ 2)⁻¹ :=
    fun s hs hs2 => numerical_smoothed_mellin_bound (1 / 2) (by norm_num) s hs hs2 ε hε hε1
  have hleft : ‖VIntegral F (15 / 16) (-T) T‖ ≤
      6144 * J * T * X ^ (15 / 16 : ℝ) / ε := by
    have hpoint (t : ℝ) (ht : t ∈ Ioc (-T) T) :
        ‖F ((15 / 16 : ℝ) + t * I)‖ ≤ J * (3072 / ε) * X ^ (15 / 16 : ℝ) := by
      have ht' : |t| ≤ T := abs_le.mpr ⟨ht.1.le, ht.2⟩
      have hll := hlog (15 / 16) t (le_refl _) (by norm_num) ht'
      have hmm := hm ((15 / 16 : ℝ) + t * I) (by norm_num) (by norm_num)
      have hn : (1 / 4 : ℝ) ≤ ‖((15 / 16 : ℝ) : ℂ) + t * I‖ ^ 2 := by
        rw [Complex.sq_norm]
        simp [Complex.normSq_apply]
        nlinarith [sq_nonneg t]
      have hi : (ε * ‖((15 / 16 : ℝ) : ℂ) + t * I‖ ^ 2)⁻¹ ≤ 4 / ε := by
        have hh := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 4) hn
        norm_num at hh
        rw [mul_inv_rev]
        change _ ≤ 4 * ε⁻¹
        simpa only [ofReal_div, ofReal_ofNat] using
          mul_le_mul_of_nonneg_right hh (inv_nonneg.mpr hε.le)
      have hmm' : ‖mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ))
          ((15 / 16 : ℝ) + t * I)‖ ≤ 3072 / ε := by
        exact hmm.trans (by calc
          _ ≤ 768 * (4 / ε) := mul_le_mul_of_nonneg_left hi (by norm_num)
          _ = _ := by ring)
      dsimp only [F, DirichletCharacter.twistedSmoothedPerronIntegrand]
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
        zero_mul, sub_self, add_zero]
      gcongr
      simpa only [neg_div, norm_neg] using hll
    rw [VIntegral, norm_smul, norm_I, one_mul]
    calc
      _ ≤ (J * (3072 / ε) * X ^ (15 / 16 : ℝ)) * |T - -T| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (by
          intro t ht
          rw [uIoc_of_le (by linarith : -T ≤ T)] at ht
          exact hpoint t ht)
      _ = _ := by rw [abs_of_nonneg (by linarith : 0 ≤ T - -T)]; ring
  have htop := norm_twistedSmoothedPerron_horizontal_le_of_logDeriv_bound
    (by norm_num : (0 : ℝ) ≤ 768) hε hm χ (by norm_num : (1 / 2 : ℝ) ≤ 15 / 16)
    (by linarith : (15 / 16 : ℝ) ≤ 1 + d) (by linarith : 1 + d ≤ 2)
    hT (abs_of_nonneg (by linarith : 0 ≤ T)) hX hJ
    (fun σ hσ hσb => hlog σ T hσ (by linarith) (le_of_eq (abs_of_nonneg (by linarith))))
  have hbottom := norm_twistedSmoothedPerron_horizontal_le_of_logDeriv_bound
    (by norm_num : (0 : ℝ) ≤ 768) hε hm χ (by norm_num : (1 / 2 : ℝ) ≤ 15 / 16)
    (by linarith : (15 / 16 : ℝ) ≤ 1 + d) (by linarith : 1 + d ≤ 2)
    hT (by rw [abs_neg, abs_of_nonneg (by linarith : 0 ≤ T)]) hX hJ
    (fun σ hσ hσb => hlog σ (-T) hσ (by linarith)
      (by rw [abs_neg, abs_of_nonneg (by linarith : 0 ≤ T)]))
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
  have hs := numerical_primitive_finite_shift χ hχ hT hd hd1 hε hε1 (by positivity : 0 < X)
  have hh := norm_verticalIntegral'_le_of_finite_contour_bounds F (by linarith) hf hs
    hleft htop hbottom ht.1 ht.2
  rw [hp]
  exact hh.trans (by dsimp only [J]; ring_nf; rfl)

#print axioms numerical_primitive_smoothed_bound
end ChenEffective
