import NumericalZetaStrip
import NumericalMellin

namespace ChenEffective
open Set Filter Complex Real MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- The principal contour's residue is explicit and uses only the local axiom. -/
theorem numerical_principal_rectangle {T d ε X : ℝ}
    (hT : 0 < T) (hd : 0 < d) (hε : 0 < ε) (hε1 : ε < 1) (hX : 0 < X) :
    let F : ℂ → ℂ := fun s => -deriv riemannZeta s / riemannZeta s *
      mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) s * (X : ℂ) ^ s
    RectangleIntegral' F ((15 / 16 : ℂ) - I * T) ((1 + d : ℝ) + I * T) =
      mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) 1 * X := by
  let z : ℂ := 15 / 16 - I * T
  let w : ℂ := (1 + d : ℝ) + I * T
  let S := z.Rectangle w
  let G : ℂ → ℂ := fun s =>
    mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) s * (X : ℂ) ^ s
  let F : ℂ → ℂ := fun s => -deriv riemannZeta s / riemannZeta s * G s
  have hRe : ∀ s ∈ S, (15 / 16 : ℝ) ≤ s.re := by
    intro s hs
    dsimp only [S] at hs
    rw [Complex.Rectangle, Complex.mem_reProdIm] at hs
    norm_num [z, w] at hs
    rw [uIcc_of_le (by linarith : (15 / 16 : ℝ) ≤ 1 + d)] at hs
    exact hs.1.1
  have hG : HolomorphicOn G S := by
    apply DifferentiableOn.mul
    · intro s hs
      exact (Smooth1MellinDifferentiable numericalSmoothing_contDiff numericalSmoothing_support
        ⟨hε, hε1⟩ (fun x _ => numericalSmoothing_nonneg x) numericalSmoothing_mass_one
        (by linarith [hRe s hs])).differentiableWithinAt
    · intro s _
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.const_cpow (by fun_prop)
      left
      exact_mod_cast hX.ne'
  have hmem : S ∈ nhds (1 : ℂ) := by
    apply rectangle_mem_nhds_iff.mpr
    rw [Complex.mem_reProdIm]
    norm_num [z, w]
    constructor
    · rw [uIoo_of_lt (by linarith : (15 / 16 : ℝ) < 1 + d)]
      constructor <;> linarith
    · rw [uIoo_of_lt (by linarith : -T < T)]
      constructor <;> linarith
  have hlog : HolomorphicOn (fun s => -deriv riemannZeta s / riemannZeta s) (S \ {1}) := by
    have hh := LogDerivZetaHoloOn (S := S \ {1}) (by simp)
      (fun s hs => zeta_ne_zero (by linarith [hRe s hs.1]) hs.2)
    convert hh.neg using 1
    ext s
    simp only [Pi.neg_apply, neg_div]
  have hF : HolomorphicOn F (S \ {1}) := hlog.mul (hG.mono sdiff_subset)
  have hn : ((fun s => -deriv riemannZeta s / riemannZeta s) -
      fun s => (1 : ℂ) * (s - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
    convert riemannZetaLogDerivResidueBigO using 1
    ext s
    simp only [one_mul, Pi.sub_apply, Pi.div_apply, Pi.neg_apply]
  have hnear := ResidueMult hG hmem hn
  have hnear' : (F - fun s => G 1 / (s - 1)) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
    convert hnear using 1
    ext s
    simp [F, Pi.mul_apply, Pi.sub_apply, div_eq_mul_inv]
  have hh := ResidueTheoremOnRectangleWithSimplePole'
    (f := F) (p := 1) (A := G 1) (z := z) (w := w)
    (by norm_num [z, w]; linarith) (by norm_num [z, w]; linarith) hmem hF hnear'
  simpa only [F, G, z, w, cpow_one, mul_assoc] using hh

#print axioms numerical_principal_rectangle
end ChenEffective
