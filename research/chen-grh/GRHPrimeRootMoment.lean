import NumericalEulerProductPower

noncomputable section
namespace ChenEffective.GRH
open Real Finset
set_option maxHeartbeats 3000000

/-- Telescoping, with no finite enumeration of integers. -/
theorem reciprocal_sqrt_sum (n : ℕ) :
    (∑ k ∈ Finset.range n, 1/sqrt ((k+1:ℕ):ℝ)) ≤ 2*sqrt (n:ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
    have hnp : (0:ℝ) < (n+1:ℕ) := by positivity
    have hs : 0 < sqrt ((n+1:ℕ):ℝ) := sqrt_pos.2 hnp
    have hm : sqrt (n:ℝ) ≤ sqrt ((n+1:ℕ):ℝ) :=
      sqrt_le_sqrt (by norm_num)
    have hsq := sq_sqrt hn
    have hsqp := sq_sqrt hnp.le
    have hdiff : 1/sqrt ((n+1:ℕ):ℝ) ≤
        2*(sqrt ((n+1:ℕ):ℝ)-sqrt (n:ℝ)) := by
      apply (div_le_iff₀ hs).mpr
      have hpos := sq_nonneg (sqrt ((n+1:ℕ):ℝ)-sqrt (n:ℝ))
      norm_num only [Nat.cast_add,Nat.cast_one] at hsqp
      norm_num only [Nat.cast_add,Nat.cast_one] at hpos ⊢
      nlinarith only [hpos,hsq,hsqp]
    linarith only [ih,hdiff]

/-- Prime reciprocal-square-root moments on one interval, from the
elementary theta upper bound; no table of primes is needed. -/
theorem prime_root_interval (F : Finset ℕ) {a b ell : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hell : 0 < ell)
    (hF : ∀ p ∈ F, p.Prime ∧ a ≤ (p:ℝ) ∧ (p:ℝ) ≤ b ∧ ell ≤ log (p:ℝ)) :
    (∑ p ∈ F, 1/sqrt (p:ℝ)) ≤ (log 4*b)/(ell*sqrt a) := by
  have hlog : (∑ p ∈ F, log (p:ℝ)) ≤ log 4*b := by
    have hh := ChenEffective.presieve_log_cost F hb
      (fun p hp => ⟨(hF p hp).1,(hF p hp).2.2.1⟩)
    rw [log_prod (fun p hp => by exact_mod_cast (hF p hp).1.ne_zero)] at hh
    exact hh
  apply (le_div_iff₀ (mul_pos hell (sqrt_pos.2 ha))).mpr
  apply le_trans _ hlog
  rw [sum_mul]
  apply sum_le_sum
  intro p hp
  have hpa := (hF p hp).2.1
  have hpl := (hF p hp).2.2.2
  have hsp : 0 < sqrt (p:ℝ) := sqrt_pos.2 (lt_of_lt_of_le ha hpa)
  have hratio : (1/sqrt (p:ℝ))*(ell*sqrt a) ≤ ell := by
    rw [one_div_mul_eq_div]
    exact (div_le_iff₀ hsp).mpr
      (mul_le_mul_of_nonneg_left (sqrt_le_sqrt hpa) hell.le)
  exact hratio.trans hpl

theorem reciprocal_sqrt_subset (F : Finset ℕ) (n : ℕ)
    (hF : ∀ k ∈ F, 1 ≤ k ∧ k ≤ n) :
    (∑ k ∈ F, 1/sqrt (k:ℝ)) ≤ 2*sqrt (n:ℝ) := by
  classical
  have hinj : Set.InjOn (fun k : ℕ => k-1) (↑F : Set ℕ) := by
    intro a ha b hb hab
    have ha1 := (hF a ha).1
    have hb1 := (hF b hb).1
    change a-1=b-1 at hab
    omega
  have hsub : F.image (fun k => k-1) ⊆ range n := by
    intro a ha
    obtain ⟨k,hk,rfl⟩ := mem_image.mp ha
    have hh := hF k hk
    apply mem_range.mpr
    omega
  calc
    _ = ∑ k ∈ F.image (fun k => k-1), 1/sqrt ((k+1:ℕ):ℝ) := by
      rw [sum_image hinj]
      apply sum_congr rfl
      intro k hk
      rw [Nat.sub_add_cancel (hF k hk).1]
    _ ≤ ∑ k ∈ range n, 1/sqrt ((k+1:ℕ):ℝ) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ _ := reciprocal_sqrt_sum n

theorem prime_root_block (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime)
    (a b : ℕ) (ha : 10000 ≤ a) :
    (∑ p ∈ F.filter (fun p => a < p ∧ p ≤ b), 1/sqrt (p:ℝ)) ≤
      ((7/5:ℝ)*b)/(8*sqrt (a:ℝ)) := by
  have hlog8 : (8:ℝ) ≤ log (10000:ℝ) := by
    exact_mod_cast (ChenEffective.log_ge_power_three (b:=8) (N:=10000) (by norm_num))
  have ha0 : (0:ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hh := prime_root_interval (F.filter (fun p => a < p ∧ p ≤ b))
    ha0 (Nat.cast_nonneg b) (by norm_num : (0:ℝ) < 8) (by
      intro p hp
      have hpF := (mem_filter.mp hp).1
      have hpi := (mem_filter.mp hp).2
      refine ⟨hF p hpF,?_,?_,?_⟩
      · exact_mod_cast (Nat.le_of_lt hpi.1)
      · exact_mod_cast hpi.2
      · apply hlog8.trans
        apply log_le_log (by norm_num)
        exact_mod_cast (ha.trans (Nat.le_of_lt hpi.1)))
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg b)
  rw [show (4:ℝ)=2^2 by norm_num,log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [log_two_lt_d9]

theorem prime_root_moment_four_million (F : Finset ℕ)
    (hF : ∀ p ∈ F, p.Prime ∧ p ≤ 4000000) :
    (∑ p ∈ F, 1/sqrt (p:ℝ)) ≤ 1700 := by
  have hsmall := reciprocal_sqrt_subset (F.filter (fun p => p ≤ 10000)) 10000
    (by intro p hp; exact ⟨(hF p (mem_filter.mp hp).1).1.one_lt.le,(mem_filter.mp hp).2⟩)
  have h1 := prime_root_block F (fun p hp => (hF p hp).1) 10000 40000 (by norm_num)
  have h2 := prime_root_block F (fun p hp => (hF p hp).1) 40000 160000 (by norm_num)
  have h3 := prime_root_block F (fun p hp => (hF p hp).1) 160000 640000 (by norm_num)
  have h4 := prime_root_block F (fun p hp => (hF p hp).1) 640000 2560000 (by norm_num)
  have h5 := prime_root_block F (fun p hp => (hF p hp).1) 2560000 4000000 (by norm_num)
  norm_num only [Nat.cast_ofNat] at hsmall h1 h2 h3 h4 h5
  have hsplit : (∑ p ∈ F, 1/sqrt (p:ℝ)) =
      (∑ p ∈ F.filter (fun p => p ≤ 10000), 1/sqrt (p:ℝ)) +
      (∑ p ∈ F.filter (fun p => 10000 < p ∧ p ≤ 40000), 1/sqrt (p:ℝ)) +
      (∑ p ∈ F.filter (fun p => 40000 < p ∧ p ≤ 160000), 1/sqrt (p:ℝ)) +
      (∑ p ∈ F.filter (fun p => 160000 < p ∧ p ≤ 640000), 1/sqrt (p:ℝ)) +
      (∑ p ∈ F.filter (fun p => 640000 < p ∧ p ≤ 2560000), 1/sqrt (p:ℝ)) +
      (∑ p ∈ F.filter (fun p => 2560000 < p ∧ p ≤ 4000000), 1/sqrt (p:ℝ)) := by
    simp only [sum_filter]
    repeat rw [← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    have hpmax := (hF p hp).2
    split_ifs
    all_goals first | omega | simp only [add_zero,zero_add]
  rw [hsplit]
  norm_num at hsmall h1 h2 h3 h4 h5
  simp only [one_div]
  linarith only [hsmall,h1,h2,h3,h4,h5]

#print axioms prime_root_moment_four_million
#print axioms prime_root_interval
#print axioms reciprocal_sqrt_subset
end ChenEffective.GRH
