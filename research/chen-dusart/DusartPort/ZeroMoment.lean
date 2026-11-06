import DusartPort.PNT.NumberTheory.LSeries.RiemannZetaHadamard
import DusartPort.XiMoment
import DusartZeroKernel

/-! A numerical absolute moment of the actual xi zero divisor, with
multiplicities. No numerical zero table or finite-height RH hypothesis. -/
noncomputable section
namespace ChenEffective
open Complex Set
open Complex.Hadamard
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

abbrev DusartXiZero := divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)

theorem dusart_xi_index_zero (p : DusartXiZero) :
    riemannXi (divisorZeroIndex₀_val p) = 0 := by
  by_contra h
  have hd := divisorZeroIndex₀_val_mem_divisor_support p
  have ha := differentiable_riemannXi.analyticAt (divisorZeroIndex₀_val p)
  have ho : analyticOrderAt riemannXi (divisorZeroIndex₀_val p) = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr h)
  rw [MeromorphicOn.divisor_apply
    (fun z _ => (differentiable_riemannXi.analyticAt z).meromorphicAt) (mem_univ _),
    ha.meromorphicOrderAt_eq, ho] at hd
  simp at hd

theorem dusart_xi_index_ne_one (p : DusartXiZero) :
    (1 : ℂ) ≠ divisorZeroIndex₀_val p := by
  intro hp
  have hz := dusart_xi_index_zero p
  rw [← hp] at hz
  have hv : riemannXi 1 = 1 / 2 := by
    simpa [riemannXi_zero] using riemannXi_one_sub (0 : ℂ)
  rw [hv] at hz
  norm_num at hz

theorem dusart_xi_zero_moment_identity :
    (∑' p : DusartXiZero,
      (1 / (1 - divisorZeroIndex₀_val p) + 1 / divisorZeroIndex₀_val p)) =
        2 * completedRiemannZeta₀ 0 := by
  obtain ⟨P, hdeg, hfac⟩ := riemannXi_hadamard_factorization_no_monomial
  have h0 := logDeriv_riemannXi_eq_polynomial_derivative_add_tsum hfac
    (z := 0) (fun p => (divisorZeroIndex₀_val_ne_zero p).symm)
  have h1 := logDeriv_riemannXi_eq_polynomial_derivative_add_tsum hfac
    (z := 1) dusart_xi_index_ne_one
  have hd : P.derivative = Polynomial.C (P.coeff 1) := by
    have hh := congrArg Polynomial.derivative (Polynomial.eq_X_add_C_of_degree_le_one hdeg)
    simpa using hh
  simp only [zero_sub, one_div, inv_neg, neg_add_cancel, tsum_zero, add_zero, hd,
    Polynomial.eval_C] at h0 h1
  calc
    _ = logDeriv riemannXi 1 - logDeriv riemannXi 0 := by rw [h1, h0]; ring
    _ = _ := dusart_xi_moment_normalization

theorem dusart_xi_zero_absolute_moment :
    Summable (fun p : DusartXiZero => ‖1 / (divisorZeroIndex₀_val p *
      (divisorZeroIndex₀_val p + 1))‖) ∧
    (∑' p : DusartXiZero, ‖1 / (divisorZeroIndex₀_val p *
      (divisorZeroIndex₀_val p + 1))‖) ≤ (3 / 25 : ℝ) := by
  have hs := summable_riemannXi_logDerivTerms_divisorZeroIndex₀ dusart_xi_index_ne_one
  have hr := (Complex.hasSum_re hs.hasSum).summable
  have hp (p : DusartXiZero) :
      ‖1 / (divisorZeroIndex₀_val p * (divisorZeroIndex₀_val p + 1))‖ ≤
        2 * (1 / (1 - divisorZeroIndex₀_val p) + 1 / divisorZeroIndex₀_val p).re := by
    have hstrip := dusart_xi_zero_strip (dusart_xi_index_zero p)
    simpa only [add_comm] using dusart_zero_kernel_norm (divisorZeroIndex₀_val p) hstrip.1 hstrip.2
  have hn := Summable.of_nonneg_of_le (fun p : DusartXiZero => norm_nonneg _) hp (hr.mul_left 2)
  refine ⟨hn, ?_⟩
  have hle := hn.tsum_le_tsum hp (hr.mul_left 2)
  have hid := congrArg Complex.re dusart_xi_zero_moment_identity
  rw [Complex.re_tsum hs] at hid
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at hid
  rw [tsum_mul_left, hid] at hle
  linarith only [hle, dusart_completed_zero_upper]

#print axioms dusart_xi_zero_moment_identity
#print axioms dusart_xi_zero_absolute_moment
end ChenEffective
