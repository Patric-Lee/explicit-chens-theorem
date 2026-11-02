import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Tactic

/-! A numerical logarithmic-derivative estimate on a zero-free disk.
The constants are independent of the function. This is intended for the
Dirichlet functions and regularized zeta on disks in the axiom's half-plane. -/
namespace ChenEffective
open Complex Set Metric Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem numerical_logDerivative_on_disk
    (f : ℂ → ℂ) (U : ℝ) (hU : 1 ≤ U)
    (hf : DifferentiableOn ℂ f (ball 0 (9 / 8)))
    (hzero : ∀ z ∈ ball (0 : ℂ) (9 / 8), f z ≠ 0)
    (hbound : ∀ z ∈ ball (0 : ℂ) (9 / 8), ‖f z‖ ≤ U)
    (hcenter : (1 / 2 : ℝ) ≤ ‖f 0‖)
    {z : ℂ} (hz : ‖z‖ ≤ 17 / 16) :
    ‖deriv f z / f z‖ ≤ 8192 * Real.log (2 * U) := by
  let S : Set ℂ := ball 0 (9 / 8)
  have hS0 : (0 : ℂ) ∈ S := mem_ball_self (by norm_num)
  let : ContractibleSpace S := (convex_ball (0 : ℂ) (9 / 8)).contractibleSpace ⟨0, hS0⟩
  have hsimply : IsSimplyConnected S := by
    change SimplyConnectedSpace S
    infer_instance
  obtain ⟨g, hgc, hgexp⟩ := Complex.exists_continuousOn_eqOn_exp_comp
    hsimply isOpen_ball hf.continuousOn (by
      rintro ⟨w, hw, heq⟩
      exact hzero w hw heq)
  have hge : ∀ w ∈ S, Complex.exp (g w) = f w := fun w hw => hgexp hw
  have hgderiv (w : ℂ) (hw : w ∈ S) : HasDerivAt g (deriv f w / f w) w := by
    have hfeq : Complex.exp ∘ g =ᶠ[𝓝 w] f :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hw) (fun v hv => hgexp hv)
    have h := (Complex.hasDerivAt_exp (g w)).of_comp_left
      (hgc.continuousAt (isOpen_ball.mem_nhds hw))
      ((hf.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt)
      (Complex.exp_ne_zero _) hfeq
    simpa only [hge w hw] using h
  let G : ℂ → ℂ := fun w => g w - g 0
  have hG (w : ℂ) (hw : w ∈ S) : HasDerivAt G (deriv f w / f w) w :=
    (hgderiv w hw).sub_const _
  have hGdiff : DifferentiableOn ℂ G S := fun w hw => (hG w hw).differentiableAt.differentiableWithinAt
  have hG0 : G 0 = 0 := sub_self _
  let M : ℝ := Real.log (2 * U)
  have hU0 : 0 < U := lt_of_lt_of_le (by norm_num) hU
  have hM : 0 < M := Real.log_pos (by linarith only [hU])
  have hGRe : Set.MapsTo G S {w : ℂ | w.re ≤ M} := by
    intro w hw
    have hexp : Real.exp (G w).re = ‖f w‖ / ‖f 0‖ := by
      rw [← Complex.norm_exp, show Complex.exp (G w) = f w / f 0 by
        dsimp [G]
        rw [Complex.exp_sub, hge w hw, hge 0 hS0], norm_div]
    have hc0 : 0 < ‖f 0‖ := lt_of_lt_of_le (by norm_num) hcenter
    have he : Real.exp (G w).re ≤ 2 * U := by
      rw [hexp]
      apply (div_le_iff₀ hc0).mpr
      have hprod := mul_le_mul_of_nonneg_left hcenter (by positivity : 0 ≤ 2 * U)
      linarith only [hbound w hw, hprod]
    have hlog := Real.log_le_log (Real.exp_pos _) he
    rwa [Real.log_exp] at hlog
  have hGbound (w : ℂ) (hw : ‖w‖ ≤ 69 / 64) : ‖G w‖ ≤ 46 * M := by
    have hwS : w ∈ S := mem_ball_zero_iff.mpr (by linarith only [hw])
    have hb := Complex.borelCaratheodory_zero hM hGdiff hGRe (by norm_num) hwS hG0
    apply hb.trans
    apply (div_le_iff₀ (by linarith only [hw] : 0 < 9 / 8 - ‖w‖)).mpr
    nlinarith only [hw, hM]
  have hzS : z ∈ S := mem_ball_zero_iff.mpr (by linarith only [hz])
  have hsmall : ball z (1 / 64) ⊆ S := by
    intro w hw
    have hd : ‖w - z‖ < 1 / 64 := by simpa only [mem_ball, dist_eq_norm] using hw
    have hn : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := norm_le_norm_sub_add w z
    apply mem_ball_zero_iff.mpr
    linarith only [hz, hd, hn]
  have hmaps : Set.MapsTo G (ball z (1 / 64)) (closedBall (G z) (92 * M)) := by
    intro w hw
    have hd : ‖w - z‖ < 1 / 64 := by simpa only [mem_ball, dist_eq_norm] using hw
    have hn : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := norm_le_norm_sub_add w z
    have hw69 : ‖w‖ ≤ 69 / 64 := by linarith only [hz, hd, hn]
    have hz69 : ‖z‖ ≤ 69 / 64 := by linarith only [hz]
    rw [mem_closedBall, dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith only [hGbound w hw69, hGbound z hz69])
  have hd := Complex.norm_deriv_le_div_of_mapsTo_ball (hGdiff.mono hsmall) hmaps (by norm_num)
  rw [(hG z hzS).deriv] at hd
  calc
    _ ≤ (92 * M) / (1 / 64) := hd
    _ ≤ 8192 * M := by nlinarith only [hM]

#print axioms numerical_logDerivative_on_disk
end ChenEffective
