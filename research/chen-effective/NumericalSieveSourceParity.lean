import NumericalSieveSourceInduction

namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers KappaOneModel
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem kernelSieveError_finset_parity (F : Finset ℕ) {b : ℕ} (hb : b ≤ 1)
    (hF : ∀ k ∈ F, k % 2 = b) : (∑ k ∈ F, kernelSieveError k) ≤ 6000 := by
  let G := F.image (fun k => k / 2)
  let M := G.sup id + 1
  have hid : (∑ j ∈ G, kernelSieveError (2 * j + b)) = ∑ k ∈ F, kernelSieveError k := by
    rw [Finset.sum_image]
    · apply sum_congr rfl
      intro k hk
      congr 1
      have hh := hF k hk
      omega
    · intro x hx y hy heq
      dsimp at heq
      have hx' := hF x hx
      have hy' := hF y hy
      omega
  have hG : G ⊆ range M := by
    intro j hj
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)
  rw [← hid]
  apply (sum_le_sum_of_subset_of_nonneg hG (fun j _ _ => kernelSieveError_nonneg (2 * j + b))).trans
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
  · simpa using kernelSieveError_even_sum_le M
  · exact kernelSieveError_odd_sum_le M

theorem source_parity_error_sum (N : ℕ) :
    (∑ n ∈ sourceParityIndices N, kernelSieveError (n - 1)) ≤ 6000 := by
  let F := (sourceParityIndices N).image (fun n => n - 1)
  have hF : ∀ k ∈ F, k % 2 = (N - 1) % 2 := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hk
    have hnp := mem_filter.mp hn
    have hnb := mem_Icc.mp hnp.1
    omega
  have hh := kernelSieveError_finset_parity F (b := (N - 1) % 2) (by omega) hF
  rw [Finset.sum_image] at hh
  · exact hh
  · intro x hx y hy heq
    dsimp at heq
    have hxb := mem_Icc.mp (mem_filter.mp hx).1
    have hyb := mem_Icc.mp (mem_filter.mp hy).1
    omega

/-- Source-native parity domination, uniform in the finite depth. The error
constant 6000 comes from proved kernel bounds and the actual layer induction. -/
theorem actual_source_parity_domination {S : BoundingSieve} {ε : ℝ}
    (hε : 0 ≤ ε) (hεcap : ε ≤ 1 / 10000) (hrelative : HasRelativeSieveProduct S ε)
    (N D z : ℕ) {s : ℝ} (hD : 1 < D) (hs : s ∈ closedDomain 2 N)
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) ≤
      suzukiVProduct S ((D : ℝ) ^ (1 / s)) *
        (finiteSourceLayer 1 2 N s + ε * 6000 * exp 2 * sieveHat s) := by
  let V := suzukiVProduct S ((D : ℝ) ^ (1 / s))
  have hV : 0 ≤ V := (suzukiVProduct_pos S _).le
  have hdom : ∀ n ∈ sourceParityIndices N, s ∈ closedDomain 2 n := by
    intro n hn
    have hpar := (mem_filter.mp hn).2
    simpa only [closedDomain, eps, hpar] using hs
  have hsum := sum_le_sum (s := sourceParityIndices N) (fun n hn =>
    actual_source_layer_domination hε hεcap hrelative n D z s hD (hdom n hn) hz)
  have hmain : (∑ n ∈ sourceParityIndices N, layer 2 n s) = finiteSourceLayer 1 2 N s := by
    unfold finiteSourceLayer sourceParityIndices
    rw [← Finset.sum_filter]
    apply sum_congr rfl
    intro n _
    exact layer_eq_suzukiLayer 2 n s
  have hsplit : (∑ n ∈ sourceParityIndices N, sourceLayerEnvelope n ε s) =
      finiteSourceLayer 1 2 N s + (ε * exp 2 * sieveHat s) *
        (∑ n ∈ sourceParityIndices N, kernelSieveError (n - 1)) := by
    have heq (n : ℕ) : sourceLayerEnvelope n ε s =
        layer 2 n s + (ε * exp 2 * sieveHat s) * kernelSieveError (n - 1) := by
      unfold sourceLayerEnvelope; ring
    simp_rw [heq]
    rw [sum_add_distrib, hmain, ← mul_sum]
  have hweight : 0 ≤ ε * exp 2 * sieveHat s := by
    have hh := (sieveHat_pos s).le
    positivity
  have herror := mul_le_mul_of_nonneg_left (source_parity_error_sum N) hweight
  rw [← mul_sum, hsplit] at hsum
  apply hsum.trans
  apply mul_le_mul_of_nonneg_left _ hV
  nlinarith only [herror]

#print axioms actual_source_parity_domination
end ChenEffective
