import GRHMomentCountKernel
import PlattCountSoundness

noncomputable section
namespace ChenEffective.GRHSub12
open Real Finset
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option maxErrors 100

theorem sumFields_eq (w Y B : ℕ) :
    sumFields w Y B = ∑ k∈range B, PsiFinite.fld (2^w) Y k := by
  induction B with
  | zero => simp [sumFields]
  | succ B ih =>
    change sumFields w Y B+PlattWindow.packedField (2^w) Y B=_
    rw [ih,sum_range_succ]
    rfl

theorem certified_segment_count {lo w B Y c : ℕ}
    (hlo : lo%2=1) (hlo3 : 3≤ lo)
    (htop : lo+2*(2^w*B)-1≤ PsiFinite.baseCover)
    (hcert : Nat.beq (PlattWindow.segmentCounts lo w B) Y=true)
    (hsum : Nat.beq (sumFields w Y B) c=true) :
    (c:ℝ)=∑ k∈range B, ∑ j∈range (2^w),
      if (lo+2*(2^w*k+j)).Prime then (1:ℝ) else 0 := by
  have hc := Nat.eq_of_beq_eq_true hcert
  have hs := Nat.eq_of_beq_eq_true hsum
  rw [←hs,sumFields_eq]
  push_cast
  apply sum_congr rfl
  intro k hk
  have h := PlattWindow.segmentCounts_prime_count hlo hlo3
    (by simpa only [Nat.mul_assoc] using htop) (mem_range.mp hk) hc
  apply h.trans
  apply sum_congr rfl
  intro j hj
  have he : PlattWindow.blockLeft lo w k+1+2*j=lo+2*(2^w*k+j) := by
    unfold PlattWindow.blockLeft
    have hh : lo-1+1=lo := Nat.sub_add_cancel (by omega)
    nlinarith only [hh]
  rw [he]

theorem prime_interval_card_le (F : Finset ℕ) (hF : ∀ p∈F,p.Prime)
    (a b lo w B c : ℕ)
    (ha : 2≤ a) (hal : a<lo) (hla : lo≤ a+2)
    (hlo : lo%2=1) (hlo3 : 3≤ lo)
    (hb : b<lo+2*(2^w*B))
    (hcount : (c:ℝ)=∑ k∈range B, ∑ j∈range (2^w),
      if (lo+2*(2^w*k+j)).Prime then (1:ℝ) else 0) :
    ((F.filter (fun p=>a<p ∧ p≤ b)).card:ℝ)≤ c := by
  classical
  let W := 2^w
  let T := F.filter (fun p=>a<p ∧ p≤ b)
  let G := ((range B)×ˢ(range W)).filter
    (fun v : ℕ×ℕ => (lo+2*(W*v.1+v.2)).Prime)
  let f := fun p : ℕ => (((p-lo)/2)/W,((p-lo)/2)%W)
  have hW : 0<W := by dsimp [W]; positivity
  have hencode (p : ℕ) (hp : p∈T) : lo+2*(W*(f p).1+(f p).2)=p := by
    have hpt := (mem_filter.mp hp).2
    have hprime := hF p (mem_filter.mp hp).1
    have hodd : p%2=1 := hprime.eq_two_or_odd.resolve_left (by omega)
    have hpl : lo≤ p := by omega
    have he : lo+2*((p-lo)/2)=p := by omega
    have hi : W*(((p-lo)/2)/W)+((p-lo)/2)%W=(p-lo)/2 := by
      have hh := Nat.mod_add_div ((p-lo)/2) W
      omega
    dsimp only [f]
    rw [hi]
    exact he
  have hmap : Set.MapsTo f (↑T : Set ℕ) (↑G : Set (ℕ×ℕ)) := by
    intro p hp
    have hpt := (mem_filter.mp hp).2
    have hprime := hF p (mem_filter.mp hp).1
    have he := hencode p hp
    have hidx : (p-lo)/2<W*B := by
      have hodd : p%2=1 := hprime.eq_two_or_odd.resolve_left (by omega)
      have hpl : lo≤ p := by omega
      have henc : lo+2*((p-lo)/2)=p := by omega
      have hb' : b<lo+2*(W*B) := hb
      omega
    apply mem_filter.mpr
    constructor
    · apply mem_product.mpr
      constructor
      · apply mem_range.mpr
        exact (Nat.div_lt_iff_lt_mul hW).mpr (by simpa only [Nat.mul_comm] using hidx)
      · exact mem_range.mpr (Nat.mod_lt _ hW)
    · rw [he]
      exact hprime
  have hinj : Set.InjOn f (↑T : Set ℕ) := by
    intro p hp q hq heq
    have he := hencode p hp
    have he' := hencode q hq
    rw [heq] at he
    omega
  have hcard := Finset.card_le_card_of_injOn f hmap hinj
  have hG : (G.card:ℝ)=∑ k∈range B,∑ j∈range W,
      if (lo+2*(W*k+j)).Prime then (1:ℝ) else 0 := by
    simp only [G,card_eq_sum_ones,sum_filter,sum_product]
    push_cast
    rfl
  have hh : (T.card:ℝ)≤ G.card := by exact_mod_cast hcard
  change (T.card:ℝ)≤ c
  rw [hG] at hh
  exact hh.trans_eq (by simpa only [W] using hcount.symm)

theorem prime_root_interval_count (F : Finset ℕ) (hF : ∀ p∈F,p.Prime)
    (r b lo w B c : ℕ) (hr : 0<r) (hr2 : 2≤ r^2)
    (hal : r^2<lo) (hla : lo≤ r^2+2) (hlo : lo%2=1) (hlo3 : 3≤ lo)
    (hb : b<lo+2*(2^w*B)) (htop : lo+2*(2^w*B)-1≤ PsiFinite.baseCover)
    (Y : ℕ) (hcert : Nat.beq (PlattWindow.segmentCounts lo w B) Y=true)
    (hsum : Nat.beq (sumFields w Y B) c=true) :
    (∑ p∈F.filter (fun p=>r^2<p ∧ p≤ b),1/sqrt (p:ℝ))≤(c:ℝ)/r := by
  have hc := prime_interval_card_le F hF (r^2) b lo w B c hr2 hal hla hlo hlo3 hb
    (certified_segment_count hlo hlo3 htop hcert hsum)
  have hr0 : (0:ℝ)<r := by exact_mod_cast hr
  have hs : (∑ p∈F.filter (fun p=>r^2<p ∧ p≤ b),1/sqrt (p:ℝ))≤
      ((F.filter (fun p=>r^2<p ∧ p≤ b)).card:ℝ)/r := by
    calc
      _ ≤ ∑ _p∈F.filter (fun p=>r^2<p ∧ p≤ b), (1:ℝ)/r := by
        apply sum_le_sum
        intro p hp
        have hpr : (r:ℝ)^2≤ p := by exact_mod_cast (mem_filter.mp hp).2.1.le
        have hroot : (r:ℝ)≤ sqrt (p:ℝ) := by
          rw [←sqrt_sq hr0.le]
          exact sqrt_le_sqrt hpr
        exact one_div_le_one_div_of_le hr0 hroot
      _ = _ := by simp [div_eq_mul_inv]
  exact hs.trans (div_le_div_of_nonneg_right hc hr0.le)

#print axioms prime_root_interval_count
end ChenEffective.GRHSub12
end
