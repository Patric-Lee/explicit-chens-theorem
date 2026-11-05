import NumericalSieveLayerDecay

/-! Upper Riemann sums for the actual continuous sieve layers.
Every grid value is a proved upper bound; no floating-point computation is
used by these theorems.
-/
noncomputable section
namespace ChenEffective
open Real Set Finset MeasureTheory intervalIntegral
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers KappaOneModel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem bjsStudy_upper_riemann_sum {f : ℝ → ℝ} {a h : ℝ} (n : ℕ)
    (hh : 0 ≤ h) (hf : ContinuousOn f (Icc a (a+n*h)))
    (hm : AntitoneOn f (Icc a (a+n*h))) :
    (∫ t in a..(a+n*h), f t) ≤ h*∑ i ∈ range n, f (a+i*h) := by
  let x : ℕ → ℝ := fun i => a+i*h
  have hcell (i : ℕ) (hi : i < n) : Icc (x i) (x (i+1)) ⊆ Icc a (a+n*h) := by
    intro t ht
    have hiR : (i+1 : ℝ) ≤ n := by exact_mod_cast hi
    have hlo : a ≤ x i := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i) hh)
    have hhi : x (i+1) ≤ a+n*h := by dsimp [x]; push_cast; nlinarith only [mul_le_mul_of_nonneg_right hiR hh]
    exact ⟨hlo.trans ht.1, ht.2.trans hhi⟩
  have hstep (i : ℕ) : x i ≤ x (i+1) := by dsimp [x]; push_cast; linarith
  have hint (i : ℕ) (hi : i < n) : IntervalIntegrable f volume (x i) (x (i+1)) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (hstep i)]
    exact hf.mono (hcell i hi)
  have hpart := sum_integral_adjacent_intervals hint
  have hsum : (∑ i ∈ range n, ∫ t in x i..x (i+1), f t) ≤
      ∑ i ∈ range n, h*f (x i) := by
    apply sum_le_sum
    intro i hi
    have hi' := mem_range.mp hi
    have hbound : (∫ t in x i..x (i+1), f t) ≤ ∫ _t in x i..x (i+1), f (x i) := by
      apply integral_mono_on (hstep i) (hint i hi') intervalIntegrable_const
      intro t ht
      exact hm (hcell i hi' ⟨le_rfl,hstep i⟩) (hcell i hi' ht) ht.1
    simpa only [intervalIntegral.integral_const, smul_eq_mul, x, Nat.cast_add, Nat.cast_one,
      show a+(i+1)*h-(a+i*h)=h by ring] using hbound
  rw [hpart] at hsum
  simpa [x, mul_sum] using hsum

theorem bjsStudy_layer_antitone (n : ℕ) :
    AntitoneOn (layer 2 n) (closedDomain 2 n) := by
  intro x hx y hy hxy
  have hreg := regular (by norm_num : (1 : ℝ) < 2) n
  have hpos := closedDomain_pos (by norm_num : (1 : ℝ) < 2) hx
  have hweighted := hreg.weighted_antitone hx hy hxy
  have hh := mul_le_mul_of_nonneg_right hxy (hreg.nonneg y hy)
  exact le_of_mul_le_mul_left (hh.trans hweighted) hpos

theorem bjsStudy_layer_zero {n : ℕ} {s : ℝ} (hs : (n : ℝ)+2 ≤ s) :
    layer 2 n s=0 := by
  rcases n with _ | _ | n
  · rfl
  · have h3 : (3 : ℝ) ≤ s := by norm_num at hs; exact hs
    simp only [layer, show (2 : ℝ)+1=3 by norm_num]
    rw [min_eq_right h3,integral_same,mul_zero]
  · have hl : lower 2 s (n+2)=(2 : ℝ)+(n+2 : ℕ) := by
      unfold lower
      apply min_eq_right
      have hbase : (2 : ℝ)+(n+2 : ℕ) ≤ s := by push_cast at hs ⊢; linarith only [hs]
      exact hbase.trans (le_max_left _ _)
    rw [layer,hl]
    simp

theorem bjsStudy_layer_integral_grid (n m : ℕ) {a h : ℝ}
    (hh : 0 ≤ h) (ha : 3-(eps n : ℝ) ≤ a) :
    (∫ t in a..(a+m*h), layer 2 n (t-1)) ≤
      h*∑ i ∈ range m, layer 2 n (a+i*h-1) := by
  have hdom : ∀ t ∈ Icc a (a+m*h), t-1 ∈ closedDomain 2 n := by
    intro t ht
    change (2 : ℝ)-(eps n : ℝ) ≤ t-1
    linarith only [ha,ht.1]
  apply bjsStudy_upper_riemann_sum m hh
  · exact (regular (by norm_num : (1 : ℝ) < 2) n).continuous.comp
      (continuous_id.sub continuous_const).continuousOn hdom
  · intro x hx y hy hxy
    exact bjsStudy_layer_antitone n (hdom x hx) (hdom y hy) (sub_le_sub_right hxy 1)

/-- The recursive grid step applies to the project's actual layers, rather
than to an unrelated scalar sequence. A subsequent integer certificate
can bound the finite sum on the right. -/
theorem bjsStudy_layer_successor_grid {n m : ℕ} (hn : 0 < n) {s h : ℝ}
    (hs : s ∈ closedDomain 2 (n+1)) (hh : 0 ≤ h)
    (ha : max s (2+(eps (n+1) : ℝ)) ≤ (n : ℝ)+3)
    (hmesh : max s (2+(eps (n+1) : ℝ))+m*h=(n : ℝ)+3) :
    layer 2 (n+1) s ≤ (h/s)*∑ i ∈ range m,
      layer 2 n (max s (2+(eps (n+1) : ℝ))+i*h-1) := by
  let a : ℝ := max s (2+(eps (n+1) : ℝ))
  have he : (eps (n+1) : ℝ)+(eps n : ℝ)=1 := by exact_mod_cast eps_succ_add n
  have hstart : 3-(eps n : ℝ) ≤ a := by
    have hmax := le_max_right s (2+(eps (n+1) : ℝ))
    dsimp [a]
    linarith only [hmax,he]
  have hq := bjsStudy_layer_integral_grid n m hh hstart
  change (∫ t in a..(a+m*h), layer 2 n (t-1)) ≤ _ at hq
  rw [show a+m*h=(n : ℝ)+3 from hmesh] at hq
  have hrec : layer 2 (n+1) s =
      s⁻¹*(∫ t in a..((n : ℝ)+3), layer 2 n (t-1)) := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [layer]
    have hl : lower 2 s (k+2)=a := by
      unfold lower
      have hb : (2 : ℝ)+(k+2 : ℕ)=(k+1 : ℕ)+3 := by push_cast; ring
      rw [hb]
      exact min_eq_left ha
    rw [hl]
    congr 2
    push_cast
    ring
  rw [hrec]
  have hp := inv_nonneg.mpr (closedDomain_pos (by norm_num : (1 : ℝ)<2) hs).le
  simpa only [a, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left hq hp

#print axioms bjsStudy_layer_integral_grid
#print axioms bjsStudy_layer_successor_grid
end ChenEffective
