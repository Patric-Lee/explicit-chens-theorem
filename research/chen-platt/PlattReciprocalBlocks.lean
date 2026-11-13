import PlattCountSoundness

noncomputable section
namespace ChenEffective.PlattWindow
open Real Finset AnalyticNumberTheory.Mertens PsiFinite
set_option maxHeartbeats 1200000

def oddReciprocalMass (A W : ℕ) : ℝ :=
  ∑ j ∈ range W, if (A+1+2*j).Prime then (1:ℝ)/(A+1+2*j:ℕ) else 0

theorem reciprocal_prefix_step (n : ℕ) :
    primeReciprocalSum (n+1) = primeReciprocalSum n+
      if (n+1).Prime then (1:ℝ)/(n+1:ℕ) else 0 := by
  simp only [primeReciprocalSum,primesUpTo,sum_filter,sum_range_succ]

/-- Recover the actual complete prime sum, rather than a surrogate count
over only the odd slots. Both block endpoints and the omitted even terms
are accounted for. -/
theorem oddReciprocalMass_eq (A : ℕ) (hA : Even A) (hA2 : 2 ≤ A) : ∀ W : ℕ,
    oddReciprocalMass A W = primeReciprocalSum (A+2*W)-primeReciprocalSum A := by
  intro W
  induction W with
  | zero => simp [oddReciprocalMass]
  | succ W ih =>
    have hev : ¬ (A+2*W+1+1).Prime := by
      intro hp
      rcases hp.eq_two_or_odd with h | h
      · omega
      · obtain ⟨k,hk⟩ := hA; omega
    have hend : A+2*(W+1)=(A+2*W+1)+1 := by ring
    rw [hend,reciprocal_prefix_step,reciprocal_prefix_step,ite_eq_right hev,add_zero]
    rw [show A+2*W+1=A+1+2*W by ring]
    unfold oddReciprocalMass at *
    rw [sum_range_succ,ih]
    ring

theorem reciprocal_segment_block {lo w B Y k : ℕ}
    (hlo : lo % 2 = 1) (hlo3 : 3 ≤ lo)
    (htop : lo+2*2^w*B-1 ≤ baseCover) (hk : k < B)
    (hcert : segmentCounts lo w B = Y) :
    ((fld (2^w) Y k:ℕ):ℝ)/(blockLeft lo w k+2*2^w:ℕ) ≤
        primeReciprocalSum (blockLeft lo w k+2*2^w)-primeReciprocalSum (blockLeft lo w k) ∧
    primeReciprocalSum (blockLeft lo w k+2*2^w)-primeReciprocalSum (blockLeft lo w k) ≤
        ((fld (2^w) Y k:ℕ):ℝ)/(blockLeft lo w k:ℕ) := by
  have hA : Even (blockLeft lo w k) := by
    apply even_iff_two_dvd.mpr
    apply Nat.dvd_of_mod_eq_zero
    dsimp [blockLeft]
    rw [show 2*2^w*k=2*(2^w*k) by ring]
    omega
  have hA2 : 2 ≤ blockLeft lo w k := by dsimp [blockLeft]; omega
  have hc := segmentCounts_prime_count hlo hlo3 htop hk hcert
  have hb := reciprocal_odd_block_bounds (W:=2^w) (by omega : 1 ≤ blockLeft lo w k)
  rw [← hc] at hb
  change _ ≤ oddReciprocalMass (blockLeft lo w k) (2^w) ∧
    oddReciprocalMass (blockLeft lo w k) (2^w) ≤ _ at hb
  rw [oddReciprocalMass_eq _ hA hA2] at hb
  exact hb

#print axioms reciprocal_segment_block
end ChenEffective.PlattWindow
