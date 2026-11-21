import GRHContourBound
import GRHZetaStrip
import NumericalPrincipalSmoothed

/-! The actual principal Perron residue and smoothed PNT estimate, shifted
to 1/2+a with a logarithmic left edge. GRH is the sole external axiom. -/
namespace ChenEffective.GRH
open Set Function Filter Complex Real MeasureTheory
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
theorem principal_rectangle {a T d ε X : ℝ} (ha : 0 < a) (ha1 : a ≤ 1/4)
    (hT : 0 < T) (hd : 0 < d) (hε : 0 < ε) (hε1 : ε < 1) (hX : 0 < X) :
    let F : ℂ → ℂ := fun s => -deriv riemannZeta s / riemannZeta s *
      mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) s * (X : ℂ) ^ s
    RectangleIntegral' F ((1/2+a : ℂ) - I * T) ((1 + d : ℝ) + I * T) =
      mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) 1 * X := by
  let z : ℂ := 1/2+a - I * T
  let w : ℂ := (1 + d : ℝ) + I * T
  let S := z.Rectangle w
  let G : ℂ → ℂ := fun s =>
    mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) s * (X : ℂ) ^ s
  let F : ℂ → ℂ := fun s => -deriv riemannZeta s / riemannZeta s * G s
  have hRe : ∀ s ∈ S, (1/2+a : ℝ) ≤ s.re := by
    intro s hs
    dsimp only [S] at hs
    rw [Complex.Rectangle, Complex.mem_reProdIm] at hs
    norm_num [z, w] at hs
    rw [uIcc_of_le (by linarith : (1/2+a : ℝ) ≤ 1 + d)] at hs
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
    · rw [uIoo_of_lt (by linarith : (1/2+a : ℝ) < 1 + d)]
      constructor <;> linarith
    · rw [uIoo_of_lt (by linarith : -T < T)]
      constructor <;> linarith
  have hlog : HolomorphicOn (fun s => -deriv riemannZeta s / riemannZeta s) (S \ {1}) := by
    have hh := LogDerivZetaHoloOn (S := S \ {1}) (by simp)
      (fun s hs => zeta_ne_zero_right (by linarith [hRe s hs.1]))
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


theorem principal_edge_log {a T : ℝ} (ha : 0 < a) (ha1 : a ≤ 1/4)
    (hT : 1 ≤ T) (s : ℂ) (hs : (1/2:ℝ)+a ≤ s.re) (hs2 : s.re ≤ 2)
    (ht : |s.im| ≤ T) (hedge : s.re = 1/2+a ∨ |s.im| = T) :
    ‖deriv riemannZeta s/riemannZeta s‖ ≤
      (64/a^2)*Real.log (32*(T+6)^2)+4 := by
  have hn : (1/4:ℝ) ≤ ‖s-1‖ := by
    rcases hedge with h | h
    · have hh := abs_re_le_norm (s-1)
      simp only [sub_re,one_re,h] at hh
      rw [abs_of_nonpos (by linarith only [ha1])] at hh
      linarith only [hh,ha1]
    · have hh := abs_im_le_norm (s-1)
      simp only [sub_im,one_im,sub_zero,h] at hh
      linarith only [hh,hT]
  have hne : s ≠ 1 := by intro h; norm_num [h] at hn
  have hi := inv_anti₀ (by norm_num : (0:ℝ)<1/4) hn
  norm_num at hi
  apply (zeta_logDerivative_gap ha (by linarith only [ha1]) s hs hs2 hne).trans
  apply add_le_add _ hi
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.log_le_log (by positivity)
  gcongr
theorem principal_smoothed_bound
    {a T d ε X : ℝ} (ha : 0 < a) (ha1 : a ≤ 1/4) (hT : 1 ≤ T) (hd : 0 < d) (hd1 : d ≤ 1)
    (hε : 0 < ε) (hε1 : ε < 1) (hX : 1 ≤ X) :
    let χ : DirichletCharacter ℂ 1 := 1
    let J := (64/a^2) * Real.log (32 * (T + 6) ^ 2) + 4
    ‖χ.twistedSmoothedPsi numericalSmoothing ε X -
      mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) 1 * X‖ ≤
      J*(4608*X^(1/2+a)*Real.log (1+T)+6144*X^(1+d)/(ε*(1+T^2))) +
      9216 * X ^ (1 + d) * (1 + d⁻¹ ^ 2) / (ε * T) := by
  let χ : DirichletCharacter ℂ 1 := 1
  let F := χ.twistedSmoothedPerronIntegrand numericalSmoothing ε X
  let J := (64/a^2) * Real.log (32 * (T + 6) ^ 2) + 4
  have hJ : 0 ≤ J := by
    have hl : 0 ≤ Real.log (32 * (T + 6) ^ 2) := by
      apply Real.log_nonneg
      nlinarith [sq_nonneg (T - 1)]
    dsimp [J]
    positivity
  have hlog (σ t : ℝ) (hσ : (1/2+a : ℝ) ≤ σ) (hσ2 : σ ≤ 2) (ht : |t| ≤ T)
      (he : σ = 1/2+a ∨ |t| = T) :
      ‖deriv χ.LFunction (σ + t * I) / χ.LFunction (σ + t * I)‖ ≤ J := by
    rw [DirichletCharacter.LFunction_modOne_eq]
    apply principal_edge_log ha ha1 hT (σ + t * I)
      (by simpa using hσ) (by simpa using hσ2) (by simpa using ht)
    simpa using he
  have hm : ∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) s‖ ≤
        768 * (ε * ‖s‖ ^ 2)⁻¹ :=
    fun s hs hs2 => numerical_smoothed_mellin_bound (1 / 2) (by norm_num) s hs hs2 ε hε hε1
  have hleft := perron_left_logarithmic χ
    (by linarith only [ha] : (1/2:ℝ) ≤ 1/2+a)
    (by linarith only [ha1] : (1/2+a:ℝ) ≤ 2) (by linarith only [hT]) hε hε1 hX hJ
    (fun t ht => hlog (1/2+a) t le_rfl (by linarith only [ha1]) ht (Or.inl rfl))
  have htop := norm_twistedSmoothedPerron_horizontal_le_of_logDeriv_bound
    (by norm_num : (0 : ℝ) ≤ 768) hε hm χ (by linarith only [ha] : (1/2:ℝ) ≤ 1/2+a)
    (by linarith only [ha1,hd] : (1/2+a:ℝ) ≤ 1+d) (by linarith : 1 + d ≤ 2)
    hT (abs_of_nonneg (by linarith : 0 ≤ T)) hX hJ
    (fun σ hσ hσb => hlog σ T hσ (by linarith)
      (le_of_eq (abs_of_nonneg (by linarith))) (Or.inr (abs_of_nonneg (by linarith))))
  have hbottom := norm_twistedSmoothedPerron_horizontal_le_of_logDeriv_bound
    (by norm_num : (0 : ℝ) ≤ 768) hε hm χ (by linarith only [ha] : (1/2:ℝ) ≤ 1/2+a)
    (by linarith only [ha1,hd] : (1/2+a:ℝ) ≤ 1+d) (by linarith : 1 + d ≤ 2)
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
  have hr : RectangleIntegral' F ((1/2+a : ℂ) - I * T) ((1 + d : ℝ) + I * T) =
      mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) 1 * X := by
    change RectangleIntegral' (fun s => -deriv χ.LFunction s / χ.LFunction s *
      mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) s * (X : ℂ) ^ s) _ _ = _
    rw [DirichletCharacter.LFunction_modOne_eq]
    exact principal_rectangle ha ha1 (lt_of_lt_of_le zero_lt_one hT) hd hε hε1
      (lt_of_lt_of_le zero_lt_one hX)
  have hh := numerical_residue_assembly F
    (mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) 1 * X)
    (a := 1/2+a) (b := 1 + d) (T := T) (le_trans zero_le_one hT)
    hf (by simpa only [ofReal_add, ofReal_div, ofReal_one, ofReal_ofNat] using hr)
    hleft htop hbottom ht.1 ht.2
  change ‖χ.twistedSmoothedPsi numericalSmoothing ε X -
    mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) 1 * X‖ ≤ _
  rw [hp]
  convert hh using 1
  ring


#print axioms principal_smoothed_bound
end ChenEffective.GRH
