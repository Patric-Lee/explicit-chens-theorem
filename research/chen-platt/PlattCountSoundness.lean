import PlattReciprocalKernel
import RSBounds.PsiFinite.BaseCert
import AnalyticNumberTheory.Mertens.Basic

noncomputable section
namespace ChenEffective.PlattWindow
open PsiFinite Finset Real
set_option maxHeartbeats 3000000

/-- A kernel-certified packed count counts all primes in each odd block.
Completeness is supplied by the independently certified base-prime sieve. -/
theorem segmentCounts_prime_count {lo w B Y k : ℕ}
    (hlo : lo % 2 = 1) (hlo3 : 3 ≤ lo)
    (htop : lo+2*2^w*B-1 ≤ baseCover) (hk : k < B)
    (hcert : segmentCounts lo w B = Y) :
    ((fld (2^w) Y k : ℕ) : ℝ) =
      ∑ j ∈ range (2^w),
        if (blockLeft lo w k+1+2*j).Prime then (1:ℝ) else 0 := by
  let W := 2^w
  let L := W*B
  let hi := lo+2*L-2
  let X := primeBitsOf lo L hi 0 basePrimes []
  have hodd : ∀ d ∈ basePrimes, d % 2 = 1 ∧ 3 ≤ d := by
    intro d hd
    have h := baseFacts.prime d hd
    exact ⟨h.2, by have := h.1.two_le; omega⟩
  have hcomp : ∀ p, p.Prime → p % 2 = 1 → p*p ≤ hi → p ∈ basePrimes := by
    intro p hp ho hpp
    apply baseFacts.complete p hp ho
    have ht : hi ≤ baseCover := by
      dsimp [hi,L,W]
      rw [show 2*(2^w*B)=2*2^w*B by ring]
      omega
    exact hpp.trans ht
  have hX : ∀ i, X.testBit i = true ↔ i < L ∧ (lo+2*i).Prime := by
    intro i
    apply primeBitsOf_testBit baseFacts.sorted hodd hcomp hlo hlo3
    intro i hiL
    dsimp [hi]
    omega
  have hcount : 2^w*(k+1) ≤ L := by
    dsimp [L,W]
    exact Nat.mul_le_mul_left _ (by omega)
  have hs := swarK_block L X w k hcount
  rw [Nat.and_two_pow_sub_one_eq_mod] at hs
  have he : fld (2^w) Y k = cnt X (2^w*k) (2^w) := by
    rw [← hcert]
    simpa only [segmentCounts, Nat.shiftLeft_eq', Nat.one_shiftLeft, Nat.mul_eq, Nat.add_eq,
      Nat.sub_eq, fld, W, L, hi, X, primeBitsOf] using hs
  rw [he]
  exact cnt_primes hX hcount (by omega)

theorem reciprocal_odd_block_bounds {A W : ℕ} (hA : 1 ≤ A) :
    (∑ j ∈ range W, if (A+1+2*j).Prime then (1:ℝ) else 0) /
        (A+2*W:ℕ) ≤
      (∑ j ∈ range W, if (A+1+2*j).Prime then (1:ℝ)/(A+1+2*j:ℕ) else 0) ∧
    (∑ j ∈ range W, if (A+1+2*j).Prime then (1:ℝ)/(A+1+2*j:ℕ) else 0) ≤
      (∑ j ∈ range W, if (A+1+2*j).Prime then (1:ℝ) else 0) / A := by
  have hA0 : (0:ℝ) < A := by exact_mod_cast hA
  rw [Finset.sum_div, Finset.sum_div]
  constructor
  · apply sum_le_sum
    intro j hj
    have hj' := mem_range.mp hj
    split_ifs
    · apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast (by omega : A+1+2*j ≤ A+2*W)
    · simp
  · apply sum_le_sum
    intro j hj
    split_ifs
    · apply one_div_le_one_div_of_le hA0
      exact_mod_cast (by omega : A ≤ A+1+2*j)
    · simp

#print axioms segmentCounts_prime_count
#print axioms reciprocal_odd_block_bounds
end ChenEffective.PlattWindow
