import GRHContourBound

/-! An actual smoothed character-prefix bound with a logarithmic left edge.
All constants and the near-critical-line shift are explicit; full Dirichlet
GRH is the only external assumption. Unsmoothing and AP aggregation are
separate subsequent steps. -/
namespace ChenEffective.GRH
open Set Function Filter Complex Real MeasureTheory
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
theorem smoothed_perron_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {a T d ε X : ℝ} (ha : 0 < a) (ha1 : a ≤ 1/4) (hT : 1 ≤ T) (hd : 0 < d) (hd1 : d ≤ 1)
    (hε : 0 < ε) (hε1 : ε < 1) (hX : 1 ≤ X) :
    ‖χ.twistedSmoothedPsi numericalSmoothing ε X‖ ≤
      ((64/a^2)*Real.log (16*(q:ℝ)*(T+4)))*
        (4608*X^(1/2+a)*Real.log (1+T)+6144*X^(1+d)/(ε*(1+T^2)))+
      9216*X^(1+d)*(1+d⁻¹^2)/(ε*T) := by
  let F := DirichletCharacter.twistedSmoothedPerronIntegrand χ numericalSmoothing ε X
  let J := (64/a^2) * Real.log (16 * (q : ℝ) * (T + 4))
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hJ : 0 ≤ J := by
    apply mul_nonneg (by positivity)
    apply Real.log_nonneg
    nlinarith only [hq, hT]
  have hlog (σ t : ℝ) (hσ : (1/2+a : ℝ) ≤ σ) (hσ2 : σ ≤ 2) (ht : |t| ≤ T) :
      ‖deriv χ.LFunction (σ + t * I) / χ.LFunction (σ + t * I)‖ ≤ J := by
    have hh := logDerivative_strip_gap χ hχ ha (by linarith only [ha1]) (σ + t * I)
      (by simpa using hσ) (by simpa using hσ2)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, zero_mul,
      add_zero, mul_one, zero_add] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by positivity) (by gcongr)) (by positivity))
  have hm : ∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) s‖ ≤
        768 * (ε * ‖s‖ ^ 2)⁻¹ :=
    fun s hs hs2 => numerical_smoothed_mellin_bound (1 / 2) (by norm_num) s hs hs2 ε hε hε1
  have hleft : ‖VIntegral F (1/2+a) (-T) T‖ ≤
      4608*J*X^(1/2+a)*Real.log (1+T) :=
    perron_left_logarithmic χ (by linarith only [ha]) (by linarith only [ha1])
      (by linarith only [hT]) hε hε1 hX hJ
      (fun t ht => hlog (1/2+a) t le_rfl (by linarith only [ha1]) ht)
  have htop := norm_twistedSmoothedPerron_horizontal_le_of_logDeriv_bound
    (by norm_num : (0 : ℝ) ≤ 768) hε hm χ (by linarith only [ha] : (1/2:ℝ) ≤ 1/2+a)
    (by linarith only [ha1,hd] : (1/2+a : ℝ) ≤ 1+d) (by linarith : 1 + d ≤ 2)
    hT (abs_of_nonneg (by linarith : 0 ≤ T)) hX hJ
    (fun σ hσ hσb => hlog σ T hσ (by linarith) (le_of_eq (abs_of_nonneg (by linarith))))
  have hbottom := norm_twistedSmoothedPerron_horizontal_le_of_logDeriv_bound
    (by norm_num : (0 : ℝ) ≤ 768) hε hm χ (by linarith only [ha] : (1/2:ℝ) ≤ 1/2+a)
    (by linarith only [ha1,hd] : (1/2+a : ℝ) ≤ 1+d) (by linarith : 1 + d ≤ 2)
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
  have hs := finite_contour_shift χ hχ ha ha1 hT hd hd1 hε hε1 (by positivity : 0 < X)
  have hh := norm_verticalIntegral'_le_of_finite_contour_bounds F (by linarith) hf hs
    hleft htop hbottom ht.1 ht.2
  rw [hp]
  exact hh.trans (by dsimp only [J]; ring_nf; rfl)


#print axioms smoothed_perron_bound
end ChenEffective.GRH
