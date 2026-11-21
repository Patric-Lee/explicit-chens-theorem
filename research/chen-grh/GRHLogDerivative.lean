import GRHAssumption
import NumericalDirichletStrip
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-! A quantitative zero-free logarithmic-derivative estimate arbitrarily
close to the critical line. The disk lemma is unconditional; only the
Dirichlet specialization uses the single full-GRH axiom. -/
namespace ChenEffective.GRH
open Complex Set Metric Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
theorem logDerivative_disk_gap
    (f : ℂ → ℂ) (U a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hU : 1 ≤ U)
    (hf : DifferentiableOn ℂ f (ball 0 (3 / 2)))
    (hzero : ∀ z ∈ ball (0 : ℂ) (3 / 2), f z ≠ 0)
    (hbound : ∀ z ∈ ball (0 : ℂ) (3 / 2), ‖f z‖ ≤ U)
    (hcenter : (1 / 2 : ℝ) ≤ ‖f 0‖)
    {z : ℂ} (hz : ‖z‖ ≤ 3 / 2-a) :
    ‖deriv f z / f z‖ ≤ (64/a^2) * Real.log (2 * U) := by
  let S : Set ℂ := ball 0 (3 / 2)
  have hS0 : (0 : ℂ) ∈ S := mem_ball_self (by norm_num)
  let : ContractibleSpace S := (convex_ball (0 : ℂ) (3 / 2)).contractibleSpace ⟨0, hS0⟩
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
  have hGbound (w : ℂ) (hw : ‖w‖ ≤ 3 / 2-a/2) : ‖G w‖ ≤ (6/a)*M := by
    have hwS : w ∈ S := mem_ball_zero_iff.mpr (by linarith only [hw,ha])
    have hb := Complex.borelCaratheodory_zero hM hGdiff hGRe (by norm_num) hwS hG0
    apply hb.trans
    have hwR : ‖w‖ ≤ (3/2:ℝ) := by linarith only [hw,ha]
    calc
      _ ≤ (3*M)/(a/2) := div_le_div₀ (by positivity)
        (by nlinarith only [mul_le_mul_of_nonneg_left hwR hM.le])
        (by positivity) (by linarith only [hw,ha])
      _ = _ := by field_simp; ring
  have hzS : z ∈ S := mem_ball_zero_iff.mpr (by linarith only [hz,ha])
  have hsmall : ball z (a/4) ⊆ S := by
    intro w hw
    have hd : ‖w - z‖ < a/4 := by simpa only [mem_ball, dist_eq_norm] using hw
    have hn : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := norm_le_norm_sub_add w z
    apply mem_ball_zero_iff.mpr
    linarith only [hz, hd, hn,ha]
  have hmaps : Set.MapsTo G (ball z (a/4)) (closedBall (G z) ((12/a)*M)) := by
    intro w hw
    have hd : ‖w - z‖ < a/4 := by simpa only [mem_ball, dist_eq_norm] using hw
    have hn : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := norm_le_norm_sub_add w z
    have hw69 : ‖w‖ ≤ 3 / 2-a/2 := by linarith only [hz, hd, hn,ha]
    have hz69 : ‖z‖ ≤ 3 / 2-a/2 := by linarith only [hz,ha]
    rw [mem_closedBall, dist_eq_norm]
    exact (norm_sub_le _ _).trans (by
      calc
        _ ≤ (6/a)*M+(6/a)*M := add_le_add (hGbound w hw69) (hGbound z hz69)
        _ = (12/a)*M := by ring)
  have hd := Complex.norm_deriv_le_div_of_mapsTo_ball (hGdiff.mono hsmall) hmaps (by positivity)
  rw [(hG z hzS).deriv] at hd
  calc
    _ ≤ ((12/a)*M) / (a/4) := hd
    _ = (48/a^2)*M := by field_simp; ring
    _ ≤ (64/a^2)*M := by gcongr <;> norm_num


theorem logDerivative_strip_gap {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (s : ℂ) (hs : (1/2:ℝ)+a ≤ s.re) (hs2 : s.re ≤ 2) :
    ‖deriv χ.LFunction s / χ.LFunction s‖ ≤
      (64/a^2) * Real.log (16 * (q : ℝ) * (|s.im| + 4)) := by
  let c : ℂ := 2 + I * s.im
  let f : ℂ → ℂ := fun z => χ.LFunction (c + z)
  let U : ℝ := 8 * (q : ℝ) * (|s.im| + 4)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hU : 1 ≤ U := by dsimp [U]; nlinarith only [hq, abs_nonneg s.im]
  have hf : DifferentiableOn ℂ f (ball 0 (3 / 2)) := by
    fun_prop
  have hRe (z : ℂ) (hz : z ∈ ball (0 : ℂ) (3 / 2)) : (1 / 2 : ℝ) < (c + z).re := by
    have hn : ‖z‖ < 3 / 2 := mem_ball_zero_iff.mp hz
    have hre := (neg_le_abs z.re).trans (abs_re_le_norm z)
    dsimp [c]
    simp only [mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self]
    linarith only [hn, hre]
  have hzero : ∀ z ∈ ball (0 : ℂ) (3 / 2), f z ≠ 0 := by
    intro z hz
    by_cases h1 : (c+z).re < 1
    · exact dirichlet_nonzero_right_in_strip q χ (c+z) (hRe z hz) h1
    · exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (le_of_not_gt h1)
  have hbound : ∀ z ∈ ball (0 : ℂ) (3 / 2), ‖f z‖ ≤ U := by
    intro z hz
    have hre := hRe z hz
    have hn : ‖z‖ < 3 / 2 := mem_ball_zero_iff.mp hz
    have hc : ‖c‖ ≤ 2 + |s.im| := by
      dsimp [c]
      simpa only [norm_ofNat, norm_mul, norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
        using norm_add_le (2 : ℂ) (I * s.im)
    have hnorm : ‖c + z‖ ≤ |s.im| + 4 := by
      have ht := norm_add_le c z
      linarith only [ht, hc, hn]
    have hratio : ‖c + z‖ / (c + z).re ≤ 2 * (|s.im| + 4) := by
      apply (div_le_iff₀ (by linarith only [hre])).mpr
      have hp := mul_le_mul_of_nonneg_left hre.le (show 0 ≤ 2 * (|s.im| + 4) by positivity)
      nlinarith only [hp, hnorm, abs_nonneg s.im]
    exact (dirichlet_L_weak_bound χ hχ (c + z) (by linarith only [hre])).trans (by
      change (q : ℝ) * (1 + ‖c + z‖ / (c + z).re) ≤ 8 * (q : ℝ) * (|s.im| + 4)
      have hp := mul_le_mul_of_nonneg_left hratio hq0
      have hp2 := mul_nonneg hq0 (abs_nonneg s.im)
      nlinarith only [hp, hq0, hp2])
  have hcenter : (1 / 2 : ℝ) ≤ ‖f 0‖ := by
    simpa only [f, add_zero, c] using dirichlet_L_at_two_lower χ s.im
  have hz : ‖s - c‖ ≤ 3/2-a := by
    have heq : s - c = ((s.re - 2 : ℝ) : ℂ) := by apply Complex.ext <;> simp [c]
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith only [hs2])]
    linarith only [hs]
  have hd := logDerivative_disk_gap f U a ha ha1 hU hf hzero hbound hcenter hz
  have hident : c + (s - c) = s := by ring
  have hderiv : deriv f (s - c) = deriv χ.LFunction s := by
    have h := ((χ.differentiable_LFunction hχ (c + (s - c))).hasDerivAt).comp (s - c)
      ((hasDerivAt_const (s - c) c).add (hasDerivAt_id (s - c)))
    simpa only [f, Function.comp_def, hident, zero_add, mul_one] using h.deriv
  simpa only [hderiv, f, hident, U, show (2 : ℝ) * (8 * (q : ℝ) * (|s.im| + 4)) =
    16 * (q : ℝ) * (|s.im| + 4) by ring] using hd


#print axioms logDerivative_disk_gap
#print axioms logDerivative_strip_gap
end ChenEffective.GRH
