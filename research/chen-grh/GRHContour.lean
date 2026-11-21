import GRHLogDerivative
import NumericalPrimitiveContour

/-! The actual finite Perron contour can now be shifted to 1/2+a,
uniformly over all nonprincipal characters, without a primitivity premise.
This is a contour identity, not yet a completed unsmoothed AP estimate. -/
namespace ChenEffective.GRH
open Set Function Filter Complex Real MeasureTheory
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
theorem finite_contour_shift {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {a T d ε X : ℝ} (ha : 0 < a) (ha1 : a ≤ 1/4) (_hT : 1 ≤ T) (hd : 0 < d) (_hd1 : d ≤ 1)
    (hε : 0 < ε) (hε1 : ε < 1) (hX : 0 < X) :
    let F := DirichletCharacter.twistedSmoothedPerronIntegrand χ numericalSmoothing ε X
    VIntegral F (1 + d) (-T) T - VIntegral F (1/2+a) (-T) T =
      HIntegral F (1/2+a) (1 + d) T - HIntegral F (1/2+a) (1 + d) (-T) := by
  let F := DirichletCharacter.twistedSmoothedPerronIntegrand χ numericalSmoothing ε X
  let z : ℂ := 1/2+a - I * T
  let w : ℂ := (1 + d : ℝ) + I * T
  have hRe : ∀ s ∈ z.Rectangle w, (1/2+a : ℝ) ≤ s.re := by
    intro s hs
    rw [Complex.Rectangle, Complex.mem_reProdIm] at hs
    norm_num [z, w] at hs
    rw [uIcc_of_le (by linarith : (1/2+a : ℝ) ≤ 1 + d)] at hs
    exact hs.1.1
  have hL : Differentiable ℂ χ.LFunction := χ.differentiable_LFunction hχ
  have hlog : HolomorphicOn (fun s => -deriv χ.LFunction s / χ.LFunction s) (z.Rectangle w) :=
    hL.deriv.differentiableOn.neg.div hL.differentiableOn (by
      intro s hs
      have hh : (1/2:ℝ) < s.re := by linarith only [hRe s hs,ha]
      by_cases h1 : s.re < 1
      · exact dirichlet_nonzero_right_in_strip q χ s hh h1
      · exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (le_of_not_gt h1))
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
  change VIntegral F (1 + d) (-T) T - VIntegral F (1/2+a) (-T) T = _
  linear_combination hz


#print axioms finite_contour_shift
end ChenEffective.GRH
