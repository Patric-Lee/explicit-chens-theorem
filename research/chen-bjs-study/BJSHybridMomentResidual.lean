import DusartPort.ZeroMoment
import BJSHybridZeroKernel
import Lean.Util.CollectAxioms

noncomputable section
namespace ChenEffective.HybridProduct
open Complex Complex.Hadamard
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def positiveXiMoment (p : DusartXiZero) : ℝ :=
  (1/(1-divisorZeroIndex₀_val p)+1/divisorZeroIndex₀_val p).re

def absoluteXiWeight (p : DusartXiZero) : ℝ :=
  ‖1/(divisorZeroIndex₀_val p*(divisorZeroIndex₀_val p+1))‖

/-- A finite head need not contain every zero below a stated height.
All omitted zeros, including any missed low or off-line zeros, are paid
by the residual positive Hadamard moment. Multiplicity is retained through
the existing divisor-zero index. No finite RH premise is used here. -/
theorem finite_head_moment_residual (s : Finset DusartXiZero) :
    (∑' p : {p : DusartXiZero // p ∉ s}, absoluteXiWeight p) ≤
      (3/2)*(2*(completedRiemannZeta₀ 0).re-∑ p ∈ s, positiveXiMoment p) := by
  classical
  have hs := summable_riemannXi_logDerivTerms_divisorZeroIndex₀ dusart_xi_index_ne_one
  have hK : Summable positiveXiMoment := (Complex.hasSum_re hs.hasSum).summable
  have hid : (∑' p, positiveXiMoment p)=2*(completedRiemannZeta₀ 0).re := by
    have hh := congrArg Complex.re dusart_xi_zero_moment_identity
    rw [Complex.re_tsum hs] at hh
    simpa only [positiveXiMoment,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
      zero_mul,sub_zero] using hh
  have hsplit := hK.sum_add_tsum_subtype_compl s
  rw [hid] at hsplit
  have hW : Summable absoluteXiWeight := dusart_xi_zero_absolute_moment.1
  have hWs : Summable (fun p : {p : DusartXiZero // p ∉ s} => absoluteXiWeight p) :=
    hW.subtype _
  have hKs : Summable (fun p : {p : DusartXiZero // p ∉ s} => positiveXiMoment p) :=
    hK.subtype _
  have hp (p : {p : DusartXiZero // p ∉ s}) :
      absoluteXiWeight p ≤ (3/2)*positiveXiMoment p := by
    have hstrip := dusart_xi_zero_strip (dusart_xi_index_zero p.1)
    dsimp only [absoluteXiWeight,positiveXiMoment]
    rw [add_comm (1/(1-divisorZeroIndex₀_val p.1)) (1/divisorZeroIndex₀_val p.1)]
    exact improved_zero_kernel_norm (divisorZeroIndex₀_val p.1) hstrip.1 hstrip.2
  have hle := hWs.tsum_le_tsum hp (hKs.mul_left (3/2))
  rw [tsum_mul_left] at hle
  linarith only [hsplit,hle]

theorem proposed_head_pays_residual (s : Finset DusartXiZero)
    (hC : 2*(completedRiemannZeta₀ 0).re ≤ (46192/1000000 : ℝ))
    (hhead : (461796/10000000 : ℝ) ≤ ∑ p ∈ s, positiveXiMoment p) :
    (∑' p : {p : DusartXiZero // p ∉ s}, absoluteXiWeight p) ≤ (19/1000000 : ℝ) := by
  have hh := finite_head_moment_residual s
  linarith only [hh,hC,hhead]

#print axioms finite_head_moment_residual

open Lean Meta in
run_elab do
  let axs ← Lean.collectAxioms ``finite_head_moment_residual
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  unless axs.size == allowed.size && axs.all allowed.contains do
    throwError "Unexpected finite-head residual axiom ledger: {axs}"
  logInfo "Finite-head residual verified: no zero-count completeness or finite RH assumption."

end ChenEffective.HybridProduct


