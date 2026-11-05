import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! Kernel-checked finite-prefix/geometric-tail certificate machinery.
This does not assume or assert any numerical BJS layer table.
-/
namespace ChenEffective
open Finset
set_option maxHeartbeats 2000000

theorem bjsStudy_geometric_tail_partial {t : ℕ → ℝ} {M : ℕ} {r : ℝ}
    (_hr0 : 0 ≤ r) (hr1 : r < 1)
    (hstep : ∀ n, M ≤ n → t (n+1) ≤ r*t n) (k : ℕ) :
    (∑ j ∈ range k, t (M+j))+t (M+k)/(1-r) ≤ t M/(1-r) := by
  have hd : 0 < 1-r := sub_pos.mpr hr1
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := div_le_div_of_nonneg_right (hstep (M+k) (by omega)) hd.le
    rw [sum_range_succ]
    have he : t (M+k)+r*t (M+k)/(1-r)=t (M+k)/(1-r) := by
      field_simp
      ring
    have hh : M+(k+1)=M+k+1 := by omega
    rw [hh]
    linarith only [ih,hs,he]

theorem bjsStudy_prefix_tail_certificate {t : ℕ → ℝ} {M : ℕ} {r C : ℝ}
    (hnonneg : ∀ n, 0 ≤ t n) (_hr0 : 0 ≤ r) (hr1 : r < 1)
    (hstep : ∀ n, M ≤ n → t (n+1) ≤ r*t n)
    (hcertificate : (∑ j ∈ range M, t j)+t M/(1-r) ≤ C) :
    ∀ n, (∑ j ∈ range n, t j) ≤ C := by
  intro n
  have hd : 0 ≤ 1-r := (sub_pos.mpr hr1).le
  by_cases hn : n ≤ M
  · apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
      (fun j _ _ => hnonneg j))
    exact (le_add_of_nonneg_right (div_nonneg (hnonneg M) hd)).trans hcertificate
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (by omega : M ≤ n)
    have ht := bjsStudy_geometric_tail_partial _hr0 hr1 hstep k
    rw [sum_range_add]
    have hlast := div_nonneg (hnonneg (M+k)) hd
    linarith only [ht,hlast,hcertificate]

#print axioms bjsStudy_prefix_tail_certificate
end ChenEffective
