import BJSDiscreteInduction

namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers KappaOneModel
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

theorem bjs_source_parity_error_sum (N : ℕ) :
    (∑ n ∈ sourceParityIndices N, bjsSharpError (n - 1)) ≤ 220 := by
  let F := (sourceParityIndices N).image (fun n => n - 1)
  have hF : ∀ k ∈ F, k % 2 = (N - 1) % 2 := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hk
    have hnp := mem_filter.mp hn
    have hnb := mem_Icc.mp hnp.1
    omega
  have hh := bjsSharpError_finset_parity F (b := (N - 1) % 2) (by omega) hF
  rw [Finset.sum_image] at hh
  · exact hh
  · intro x hx y hy heq
    dsimp at heq
    have hxb := mem_Icc.mp (mem_filter.mp hx).1
    have hyb := mem_Icc.mp (mem_filter.mp hy).1
    omega

/-- Source-native parity domination, uniform in the finite depth. The error
constant 220 comes from proved kernel bounds and the actual layer induction. -/
theorem bjs_actual_source_parity_domination {S : BoundingSieve} {ε : ℝ}
    (hε : 0 ≤ ε) (hεcap : ε ≤ 1 / 4000) (hrelative : HasRelativeSieveProduct S ε)
    (N D z : ℕ) {s : ℝ} (hD : 1 < D) (hs : s ∈ closedDomain 2 N)
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) ≤
      suzukiVProduct S ((D : ℝ) ^ (1 / s)) *
        (finiteSourceLayer 1 2 N s + ε * 220 * exp 2 * sieveHat s) := by
  let V := suzukiVProduct S ((D : ℝ) ^ (1 / s))
  have hV : 0 ≤ V := (suzukiVProduct_pos S _).le
  have hdom : ∀ n ∈ sourceParityIndices N, s ∈ closedDomain 2 n := by
    intro n hn
    have hpar := (mem_filter.mp hn).2
    simpa only [closedDomain, eps, hpar] using hs
  have hsum := sum_le_sum (s := sourceParityIndices N) (fun n hn =>
    bjs_actual_source_layer_domination hε hεcap hrelative n D z s hD (hdom n hn) hz)
  have hmain : (∑ n ∈ sourceParityIndices N, layer 2 n s) = finiteSourceLayer 1 2 N s := by
    unfold finiteSourceLayer sourceParityIndices
    rw [← Finset.sum_filter]
    apply sum_congr rfl
    intro n _
    exact layer_eq_suzukiLayer 2 n s
  have hsplit : (∑ n ∈ sourceParityIndices N, bjsLayerEnvelope n ε s) =
      finiteSourceLayer 1 2 N s + (ε * exp 2 * sieveHat s) *
        (∑ n ∈ sourceParityIndices N, bjsSharpError (n - 1)) := by
    have heq (n : ℕ) : bjsLayerEnvelope n ε s =
        layer 2 n s + (ε * exp 2 * sieveHat s) * bjsSharpError (n - 1) := by
      unfold bjsLayerEnvelope; ring
    simp_rw [heq]
    rw [sum_add_distrib, hmain, ← mul_sum]
  have hweight : 0 ≤ ε * exp 2 * sieveHat s := by
    have hh := (sieveHat_pos s).le
    positivity
  have herror := mul_le_mul_of_nonneg_left (bjs_source_parity_error_sum N) hweight
  rw [← mul_sum, hsplit] at hsum
  apply hsum.trans
  apply mul_le_mul_of_nonneg_left _ hV
  nlinarith only [herror]


#print axioms bjs_actual_source_parity_domination
end ChenEffective
