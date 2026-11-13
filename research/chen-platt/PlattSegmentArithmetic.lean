import PlattReciprocalBlocks

noncomputable section
namespace ChenEffective.PlattWindow
open Real Finset AnalyticNumberTheory.Mertens PsiFinite
set_option maxHeartbeats 1800000

theorem segmentFixed_eq (scale lo w Y n : ℕ) :
    segmentFixed scale lo w Y n =
      (∑ k ∈ range n,(reciprocalFloors scale lo w Y k).1,
       ∑ k ∈ range n,(reciprocalFloors scale lo w Y k).2) := by
  induction n with
  | zero => simp [segmentFixed]
  | succ n ih => simp only [segmentFixed,ih,sum_range_succ]

theorem reciprocalFloors_bounds {scale lo w B Y k : ℕ}
    (hlo : lo % 2 = 1) (hlo3 : 3 ≤ lo)
    (htop : lo+2*2^w*B-1 ≤ baseCover) (hk : k < B)
    (hcert : segmentCounts lo w B = Y) :
    ((reciprocalFloors scale lo w Y k).1:ℝ) ≤
        scale*(primeReciprocalSum (blockLeft lo w k+2*2^w)-primeReciprocalSum (blockLeft lo w k)) ∧
    scale*(primeReciprocalSum (blockLeft lo w k+2*2^w)-primeReciprocalSum (blockLeft lo w k)) ≤
        ((reciprocalFloors scale lo w Y k).2:ℝ) := by
  have hA : 0 < blockLeft lo w k := by dsimp [blockLeft]; omega
  have hb := reciprocal_segment_block hlo hlo3 htop hk hcert
  have hS : (0:ℝ) ≤ scale := Nat.cast_nonneg scale
  have h1 := mul_le_mul_of_nonneg_left hb.1 hS
  have h2 := mul_le_mul_of_nonneg_left hb.2 hS
  have hf := (TernaryGoldbach.Prelim.LogWalk.floor_div_bounds
    (scale*fld (2^w) Y k) (blockLeft lo w k+2*2^w) (by omega)).1
  have hu := (TernaryGoldbach.Prelim.LogWalk.floor_div_bounds
    (scale*fld (2^w) Y k) (blockLeft lo w k) hA).2
  simp only [Nat.cast_mul,mul_div_assoc] at hf hu
  constructor
  · exact hf.trans h1
  · simpa only [reciprocalFloors,packedField,fld,Nat.cast_add,Nat.cast_one] using h2.trans hu

theorem reciprocal_blocks_telescope (lo w B : ℕ) :
    (∑ k ∈ range B, (primeReciprocalSum (blockLeft lo w k+2*2^w)-primeReciprocalSum (blockLeft lo w k))) =
      primeReciprocalSum (lo-1+2*2^w*B)-primeReciprocalSum (lo-1) := by
  induction B with
  | zero => simp [blockLeft]
  | succ n ih =>
    rw [sum_range_succ,ih]
    have e : blockLeft lo w n+2*2^w=lo-1+2*2^w*(n+1) := by dsimp [blockLeft]; ring
    rw [e]
    unfold blockLeft
    ring

/-- Integer replay of a whole segment bounds the genuine reciprocal-prime
increment. The sieve and integer arithmetic certificates are separate. -/
theorem segment_reciprocal_certificate {scale lo w B Y Qlo Qhi : ℕ}
    (hlo : lo % 2 = 1) (hlo3 : 3 ≤ lo)
    (htop : lo+2*2^w*B-1 ≤ baseCover)
    (hcert : segmentCounts lo w B = Y)
    (harith : segmentFixed scale lo w Y B = (Qlo,Qhi)) :
    (Qlo:ℝ) ≤ scale*(primeReciprocalSum (lo-1+2*2^w*B)-primeReciprocalSum (lo-1)) ∧
    scale*(primeReciprocalSum (lo-1+2*2^w*B)-primeReciprocalSum (lo-1)) ≤ (Qhi:ℝ) := by
  have hL := sum_le_sum (s:=range B) (fun k hk =>
    (reciprocalFloors_bounds (scale:=scale) hlo hlo3 htop (mem_range.mp hk) hcert).1)
  have hU := sum_le_sum (s:=range B) (fun k hk =>
    (reciprocalFloors_bounds (scale:=scale) hlo hlo3 htop (mem_range.mp hk) hcert).2)
  have he := (segmentFixed_eq scale lo w Y B).symm.trans harith
  have hl := congrArg Prod.fst he
  have hu := congrArg Prod.snd he
  change (∑ k ∈ range B,(reciprocalFloors scale lo w Y k).1)=Qlo at hl
  change (∑ k ∈ range B,(reciprocalFloors scale lo w Y k).2)=Qhi at hu
  simp only [← Finset.mul_sum,reciprocal_blocks_telescope,← Nat.cast_sum,hl,hu] at hL hU
  exact ⟨hL,hU⟩

#print axioms segment_reciprocal_certificate
end ChenEffective.PlattWindow
