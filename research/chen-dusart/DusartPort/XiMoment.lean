import DusartPort.PNT.Analysis.SpecialFunctions.CompletedXi
import DusartPort.PNT.NumberTheory.LSeries.RiemannZetaValues
import ExplicitSiegel

/-! Normalization and zero strip for the positive xi zero moment.
The logarithmic-derivative identity here is a scalar identity; the
Hadamard theorem is still required to identify it with the sum over zeros. -/
noncomputable section
namespace ChenEffective
open Complex Real
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem dusart_xi_deriv_zero :
    deriv riemannXi 0 = -completedRiemannZeta₀ 0 / 2 := by
  have ha : HasDerivAt (fun s : ℂ => s * (s - 1)) (-1) 0 := by
    convert! (hasDerivAt_id' (0 : ℂ)).mul ((hasDerivAt_id' (0 : ℂ)).sub_const 1) using 1
    norm_num
  have hh : HasDerivAt riemannXi (-completedRiemannZeta₀ 0 / 2) 0 := by
    convert! ((ha.mul (differentiable_completedZeta₀ 0).hasDerivAt).add_const 1).div_const 2 using 1
    simp
  exact hh.deriv

theorem dusart_xi_logDeriv_zero :
    logDeriv riemannXi 0 = -completedRiemannZeta₀ 0 := by
  rw [logDeriv_apply, dusart_xi_deriv_zero, riemannXi_zero]
  ring

theorem dusart_xi_logDeriv_one :
    logDeriv riemannXi 1 = completedRiemannZeta₀ 0 := by
  have hh := ((differentiable_riemannXi (1 - 1)).hasDerivAt).comp (1 : ℂ)
    ((hasDerivAt_id' (1 : ℂ)).const_sub 1)
  have heq : (fun s : ℂ => riemannXi (1 - s)) = riemannXi := funext riemannXi_one_sub
  have hd : deriv riemannXi 1 = -deriv riemannXi 0 := by
    have hd0 := hh.deriv
    change deriv (fun s : ℂ => riemannXi (1 - s)) 1 =
      deriv riemannXi (1 - 1) * (-1) at hd0
    rw [heq] at hd0
    simpa using hd0
  have hv : riemannXi 1 = 1 / 2 := by
    simpa [riemannXi_zero] using riemannXi_one_sub (0 : ℂ)
  rw [logDeriv_apply, hd, hv, dusart_xi_deriv_zero]
  ring

theorem dusart_xi_moment_normalization :
    logDeriv riemannXi 1 - logDeriv riemannXi 0 = 2 * completedRiemannZeta₀ 0 := by
  rw [dusart_xi_logDeriv_one, dusart_xi_logDeriv_zero]
  ring

theorem dusart_xi_ne_zero_right {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) :
    riemannXi s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst s
    have hh := riemannXi_one_sub (0 : ℂ)
    norm_num [riemannXi_zero] at hh
    rw [hh]
    norm_num
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hz := zeta_ne_zero hs hs1
  have hc : completedRiemannZeta s ≠ 0 := by
    intro h
    apply hz
    rw [riemannZeta_def_of_ne_zero hs0, h, zero_div]
  rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) hc) (by norm_num)

theorem dusart_xi_zero_strip {ρ : ℂ} (hρ : riemannXi ρ = 0) :
    (1 / 8 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 7 / 8 := by
  have hhi : ρ.re ≤ 7 / 8 := by
    by_contra h
    exact dusart_xi_ne_zero_right (lt_of_not_ge h) hρ
  have hlo : (1 / 8 : ℝ) ≤ ρ.re := by
    by_contra h
    have hh : (7 / 8 : ℝ) < (1 - ρ).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith only [lt_of_not_ge h]
    exact dusart_xi_ne_zero_right hh (by rw [riemannXi_one_sub, hρ])
  exact ⟨hlo, hhi⟩

theorem dusart_gamma_upper : Real.eulerMascheroniConstant < (59 / 100 : ℝ) := by
  have hg := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 64
  simp only [Real.eulerMascheroniSeq', show ¬(64 : ℕ) = 0 by decide, if_false] at hg
  norm_num only [Nat.cast_ofNat] at hg
  have hh : (harmonic 64 : ℝ) ≤ (949 / 200 : ℝ) := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hl : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hl] at hg
  linarith only [hg, hh, Real.log_two_gt_d9]

theorem dusart_log_four_pi_lower : (253 / 100 : ℝ) ≤ Real.log (4 * Real.pi) := by
  have hh := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 107 / 207)
    (by norm_num : (107 / 207 : ℝ) < 1) 8
  norm_num [Finset.sum_range_succ] at hh
  have hp := Real.log_le_log (by norm_num : (0 : ℝ) < 157 / 50)
    (show (157 / 50 : ℝ) ≤ Real.pi by linarith only [Real.pi_gt_d2])
  have hid : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num) Real.pi_pos.ne',
      show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hid]
  linarith only [hh, hp, Real.log_two_gt_d9]

theorem dusart_completed_zero_upper : (completedRiemannZeta₀ 0).re ≤ (3 / 100 : ℝ) := by
  rw [completedRiemannZeta₀_zero]
  have hl : (Complex.log (4 * (Real.pi : ℂ))).re = Real.log (4 * Real.pi) := by
    have he : (4 * (Real.pi : ℂ)) = ((4 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
    rw [he, ← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ 4 * Real.pi)]
    rfl
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.sub_re, Complex.ofReal_re,
    Complex.one_re]
  rw [hl]
  linarith only [dusart_gamma_upper, dusart_log_four_pi_lower]

#print axioms dusart_xi_moment_normalization
#print axioms dusart_xi_zero_strip
#print axioms dusart_completed_zero_upper
end ChenEffective
