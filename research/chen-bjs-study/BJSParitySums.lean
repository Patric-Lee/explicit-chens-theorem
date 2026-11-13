import BJSLayerProfile

noncomputable section
namespace ChenEffective
open Real Finset
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

def bjsSharpStepRate (k : ℕ) : ℝ := if k%2=0 then 1931/2000 else 1859/2000

def bjsSharpError : ℕ → ℝ
  | 0 => 3
  | k+1 => bjsSharpStepRate k*bjsSharpError k+
      (367/50 : ℝ)*bjsSharpProfile (k+1)+(401/100 : ℝ)*bjsSharpProfile (k+2)

theorem bjsSharpError_nonneg (k : ℕ) : 0 ≤ bjsSharpError k := by
  induction k with
  | zero => norm_num [bjsSharpError]
  | succ k ih =>
    have hr : 0 ≤ bjsSharpStepRate k := by unfold bjsSharpStepRate; split <;> norm_num
    have h1 := bjsSharpProfile_nonneg (k+1)
    have h2 := bjsSharpProfile_nonneg (k+2)
    simp only [bjsSharpError]
    positivity

def bjsParityTWeight (b k : ℕ) : ℝ :=
  if b=0 then (if k%2=0 then 1 else 1859/2000)/(1-(1931/2000 : ℝ)*(1859/2000))
  else (if k%2=0 then 1931/2000 else 1)/(1-(1931/2000 : ℝ)*(1859/2000))

def bjsParityAWeight (b k : ℕ) : ℝ :=
  ((367/50 : ℝ)+(401/100)*(241/250))*
    (bjsParityTWeight b (k+1)+(241/250)*bjsParityTWeight b k)/(1-(241/250 : ℝ)^2)

def bjsParityPotential (b k : ℕ) : ℝ :=
  bjsParityTWeight b k*bjsSharpError k+bjsParityAWeight b k*bjsSharpProfile (k+1)

theorem bjsParityPotential_nonneg (b k : ℕ) : 0 ≤ bjsParityPotential b k := by
  have ht (j : ℕ) : 0 ≤ bjsParityTWeight b j := by
    unfold bjsParityTWeight
    split <;> split <;> norm_num
  have ha : 0 ≤ bjsParityAWeight b k := by
    unfold bjsParityAWeight
    have h0 := ht k
    have h1 := ht (k+1)
    positivity
  exact add_nonneg (mul_nonneg (ht k) (bjsSharpError_nonneg k))
    (mul_nonneg ha (bjsSharpProfile_nonneg (k+1)))

theorem bjsParityPotential_step (b k : ℕ) (hb : b≤1) (hk : 11≤k) :
    bjsParityPotential b k=(if k%2=b then bjsSharpError k else 0)+bjsParityPotential b (k+1) := by
  have hp := bjsSharpProfile_step (n:=k+1) (by omega)
  have hk2 : (k+2)%2=k%2 := by omega
  have hk1 : (k+1)%2=1-k%2 := by omega
  simp only [bjsParityPotential,bjsSharpError,bjsParityAWeight,bjsParityTWeight,bjsSharpStepRate,hp,hk2,hk1]
  rcases (show b=0 ∨ b=1 by omega) with rfl | rfl <;>
    rcases (show k%2=0 ∨ k%2=1 by omega) with he | he <;>
    simp only [he] <;> norm_num <;> ring

theorem bjsParityPotential_prefix (b : ℕ) (hb : b≤1) :
    (∑ j ∈ range 11, if j%2=b then bjsSharpError j else 0)+bjsParityPotential b 11 ≤ 220 := by
  rcases (show b=0 ∨ b=1 by omega) with rfl | rfl <;>
    norm_num [Finset.sum_range_succ,bjsParityPotential,bjsParityAWeight,bjsParityTWeight,
      bjsSharpError,bjsSharpStepRate,bjsSharpProfile,bjsGridProfileNumerators]

theorem bjsParityPotential_tail (b m : ℕ) (hb : b≤1) :
    (∑ j ∈ range m, if (11+j)%2=b then bjsSharpError (11+j) else 0)+
      bjsParityPotential b (11+m)=bjsParityPotential b 11 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hs := bjsParityPotential_step b (11+m) hb (by omega)
    have hid : 11+(m+1)=11+m+1 := by omega
    rw [hid]
    linarith only [ih,hs]

theorem bjsSharpError_parity_partial (b m : ℕ) (hb : b≤1) :
    (∑ j ∈ range m, if j%2=b then bjsSharpError j else 0) ≤ 220 := by
  have hp := bjsParityPotential_prefix b hb
  by_cases hm : m≤11
  · have hs : (∑ j ∈ range m, if j%2=b then bjsSharpError j else 0) ≤
        ∑ j ∈ range 11, if j%2=b then bjsSharpError j else 0 := by
      apply sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
      intro j _ _
      split <;> first | exact bjsSharpError_nonneg j | norm_num
    linarith only [hs,hp,bjsParityPotential_nonneg b 11]
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (by omega : 11≤m)
    rw [sum_range_add]
    have ht := bjsParityPotential_tail b k hb
    linarith only [ht,hp,bjsParityPotential_nonneg b (11+k)]

theorem bjsSharpError_finset_parity (F : Finset ℕ) {b : ℕ} (hb : b≤1)
    (hF : ∀ k∈F, k%2=b) : (∑ k∈F, bjsSharpError k) ≤ 220 := by
  let M := F.sup id+1
  have hsub : F ⊆ range M := by
    intro k hk
    exact mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f:=id) hk))
  have heq : (∑ k∈F, bjsSharpError k)=∑ k∈F, if k%2=b then bjsSharpError k else 0 := by
    apply sum_congr rfl
    intro k hk
    rw [if_pos (hF k hk)]
  rw [heq]
  apply (sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => ?_)).trans (bjsSharpError_parity_partial b M hb)
  split <;> first | exact bjsSharpError_nonneg k | norm_num

#print axioms bjsSharpError_finset_parity
end ChenEffective
