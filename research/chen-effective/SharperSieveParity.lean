import NumericalSieveSourceParity

namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers KappaOneModel
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

private noncomputable def sharpKernelPotential (x : ℝ) (n : ℕ) : ℝ :=
  (x + 12 * ((965 / 1000 : ℝ) + 964 / 1000) *
    (964 / 1000 : ℝ) ^ n / (1 - (964 / 1000 : ℝ) ^ 2)) /
    (1 - (965 / 1000 : ℝ) ^ 2)

private theorem sharpKernelPotential_step (n : ℕ) :
    sharpKernelPotential (kernelSieveError n) n = kernelSieveError n +
      sharpKernelPotential (kernelSieveError (n + 2)) (n + 2) := by
  simp only [sharpKernelPotential, kernelSieveError, pow_succ]
  ring

theorem sharp_kernel_even_partial (m : ℕ) :
    (∑ j ∈ range m, kernelSieveError (2 * j)) +
      sharpKernelPotential (kernelSieveError (2 * m)) (2 * m) =
        sharpKernelPotential (kernelSieveError 0) 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have h := sharpKernelPotential_step (2 * m)
    rw [show 2 * (m + 1) = 2 * m + 2 by omega]
    linarith

theorem sharp_kernel_even_sum_le (m : ℕ) :
    (∑ j ∈ range m, kernelSieveError (2 * j)) ≤ 4806 := by
  have h := sharp_kernel_even_partial m
  have hp : 0 ≤ sharpKernelPotential (kernelSieveError (2 * m)) (2 * m) := by
    have hx := kernelSieveError_nonneg (2 * m)
    unfold sharpKernelPotential
    positivity
  have h0 : sharpKernelPotential (kernelSieveError 0) 0 ≤ 4806 := by
    norm_num [sharpKernelPotential, kernelSieveError]
  linarith

theorem sharp_kernel_odd_partial (m : ℕ) :
    (∑ j ∈ range m, kernelSieveError (2 * j + 1)) +
      sharpKernelPotential (kernelSieveError (2 * m + 1)) (2 * m + 1) =
        sharpKernelPotential (kernelSieveError 1) 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have h := sharpKernelPotential_step (2 * m + 1)
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega]
    linarith

theorem sharp_kernel_odd_sum_le (m : ℕ) :
    (∑ j ∈ range m, kernelSieveError (2 * j + 1)) ≤ 4806 := by
  have h := sharp_kernel_odd_partial m
  have hp : 0 ≤ sharpKernelPotential (kernelSieveError (2 * m + 1)) (2 * m + 1) := by
    have hx := kernelSieveError_nonneg (2 * m + 1)
    unfold sharpKernelPotential
    positivity
  have h0 : sharpKernelPotential (kernelSieveError 1) 1 ≤ 4806 := by
    norm_num [sharpKernelPotential, kernelSieveError]
  linarith

theorem sharp_kernel_finset_parity (F : Finset ℕ) {b : ℕ} (hb : b ≤ 1)
    (hF : ∀ k ∈ F, k % 2 = b) : (∑ k ∈ F, kernelSieveError k) ≤ 4806 := by
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
  · simpa using sharp_kernel_even_sum_le M
  · exact sharp_kernel_odd_sum_le M

theorem sharp_source_parity_error_sum (N : ℕ) :
    (∑ n ∈ sourceParityIndices N, kernelSieveError (n - 1)) ≤ 4806 := by
  let F := (sourceParityIndices N).image (fun n => n - 1)
  have hF : ∀ k ∈ F, k % 2 = (N - 1) % 2 := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hk
    have hnp := mem_filter.mp hn
    have hnb := mem_Icc.mp hnp.1
    omega
  have hh := sharp_kernel_finset_parity F (b := (N - 1) % 2) (by omega) hF
  rw [Finset.sum_image] at hh
  · exact hh
  · intro x hx y hy heq
    dsimp at heq
    have hxb := mem_Icc.mp (mem_filter.mp hx).1
    have hyb := mem_Icc.mp (mem_filter.mp hy).1
    omega

/-- Source-native parity domination, uniform in the finite depth. The error
constant 4806 comes from proved kernel bounds and the actual layer induction. -/
theorem sharp_actual_source_parity_domination {S : BoundingSieve} {ε : ℝ}
    (hε : 0 ≤ ε) (hεcap : ε ≤ 1 / 10000) (hrelative : HasRelativeSieveProduct S ε)
    (N D z : ℕ) {s : ℝ} (hD : 1 < D) (hs : s ∈ closedDomain 2 N)
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) ≤
      suzukiVProduct S ((D : ℝ) ^ (1 / s)) *
        (finiteSourceLayer 1 2 N s + ε * 4806 * exp 2 * sieveHat s) := by
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
  have herror := mul_le_mul_of_nonneg_left (sharp_source_parity_error_sum N) hweight
  rw [← mul_sum, hsplit] at hsum
  apply hsum.trans
  apply mul_le_mul_of_nonneg_left _ hV
  nlinarith only [herror]


#print axioms sharp_actual_source_parity_domination
end ChenEffective
