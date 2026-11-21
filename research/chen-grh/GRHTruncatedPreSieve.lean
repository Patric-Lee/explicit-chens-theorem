import NumericalPreSieveRemainder

/-! Truncation of the exact pre-sieve expansion.  The tail is controlled by
weighted moments rather than by the size of the entire prime product.
All estimates in this file are elementary; no GRH hypothesis is used. -/
noncomputable section
namespace ChenEffective.GRH
open Real Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.LinearSieve
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem reciprocal_tail_rankin (F : Finset ℕ) (C : ℕ) (hC : 0 < C)
    (f : ℕ → ℝ) (hf : ∀ a ∈ F, 0 ≤ f a) :
    (∑ a ∈ F.filter (fun a => C < a), f a) ≤
      (∑ a ∈ F, sqrt (a:ℝ)*f a)/sqrt (C:ℝ) := by
  have hCp : (0:ℝ) < C := by exact_mod_cast hC
  apply (le_div_iff₀ (sqrt_pos.2 hCp)).mpr
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ a ∈ F.filter (fun a => C < a), sqrt (a:ℝ)*f a := by
      apply sum_le_sum
      intro a ha
      have hca : (C:ℝ) ≤ a := by
        exact_mod_cast (Nat.le_of_lt (mem_filter.mp ha).2)
      nlinarith only [mul_le_mul_of_nonneg_right (sqrt_le_sqrt hca)
        (hf a (mem_filter.mp ha).1)]
    _ ≤ ∑ a ∈ F, sqrt (a:ℝ)*f a :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun a ha _ => mul_nonneg (sqrt_nonneg _) (hf a ha))

theorem preSieve_rem_truncated (S : BoundingSieve) (U : ℝ) {d C : ℕ}
    (hd : d ∣ restrictedSievePrimeProduct S U) (hC : 0 < C) :
    |(preSieveCounting S U).rem d| ≤
      (∑ a ∈ (smallSievePrimeProduct S U).divisors.filter (fun a => a ≤ C),
        |S.rem (a*d)|) +
      (∑ a ∈ (smallSievePrimeProduct S U).divisors,
        sqrt (a:ℝ)*|S.rem (a*d)|)/sqrt (C:ℝ) := by
  have hsplit := sum_filter_add_sum_filter_not
    (smallSievePrimeProduct S U).divisors (fun a => a ≤ C)
    (fun a => |S.rem (a*d)|)
  have htail := reciprocal_tail_rankin (smallSievePrimeProduct S U).divisors C hC
    (fun a => |S.rem (a*d)|) (fun _ _ => abs_nonneg _)
  simp only [not_le] at hsplit
  exact (preSieveCounting_rem_abs S U hd).trans (by linarith only [hsplit,htail])

/-- A useful form for the application: only small divisors use AP
distribution. Large divisors are paid for using reciprocal and density
moments. The pointwise majorant is an explicit premise, not an axiom. -/
theorem preSieve_rem_truncated_moments (S : BoundingSieve) (U : ℝ) {d C : ℕ}
    (hd : d ∣ restrictedSievePrimeProduct S U) (hC : 0 < C)
    (A B : ℝ) (v : ℕ → ℝ)
    (hrem : ∀ a ∈ (smallSievePrimeProduct S U).divisors,
      |S.rem (a*d)| ≤ A/(a:ℝ)+B*v a) :
    |(preSieveCounting S U).rem d| ≤
      (∑ a ∈ (smallSievePrimeProduct S U).divisors.filter (fun a => a ≤ C),
        |S.rem (a*d)|) +
      (A*(∑ a ∈ (smallSievePrimeProduct S U).divisors, sqrt (a:ℝ)/(a:ℝ)) +
       B*(∑ a ∈ (smallSievePrimeProduct S U).divisors, sqrt (a:ℝ)*v a))/
        sqrt (C:ℝ) := by
  apply (preSieve_rem_truncated S U hd hC).trans
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ (sqrt_nonneg _)
  calc
    _ ≤ ∑ a ∈ (smallSievePrimeProduct S U).divisors,
        sqrt (a:ℝ)*(A/(a:ℝ)+B*v a) := by
      apply sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (hrem a ha) (sqrt_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
      apply sum_congr rfl
      intro a ha
      ring

/-- Full finite error assembly with a truncated distribution range `C*D`.
The discarded divisors are retained explicitly as a weighted moment. -/
theorem preSieve_errSum_truncated (S : BoundingSieve) (U : ℝ) (D C : ℕ)
    (hC : 0 < C) (weight : ℕ → ℝ)
    (hsupp : ∀ d, d ∣ restrictedSievePrimeProduct S U → ¬d < D → weight d = 0)
    (hweight : ∀ d, d ∣ restrictedSievePrimeProduct S U → |weight d| ≤ 1) :
    (preSieveCounting S U).errSum weight ≤ sieveRemainderBelow S (C*D) +
      (∑ d ∈ (restrictedSievePrimeProduct S U).divisors.filter (fun d => d < D),
        ∑ a ∈ (smallSievePrimeProduct S U).divisors,
          sqrt (a:ℝ)*|S.rem (a*d)|)/sqrt (C:ℝ) := by
  let Q := smallSievePrimeProduct S U
  let R := restrictedSievePrimeProduct S U
  let A := Q.divisors.filter (fun a => a ≤ C)
  let B := R.divisors.filter (fun d => d < D)
  let T := A ×ˢ B
  have hcop : Q.Coprime R := sieve_prime_partition_coprime S U
  have hfull : T ⊆ Q.divisors ×ˢ R.divisors := by
    intro x hx
    exact mem_product.mpr ⟨(mem_filter.mp (mem_product.mp hx).1).1,
      (mem_filter.mp (mem_product.mp hx).2).1⟩
  have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1*x.2) (↑T : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    exact hcop.mul_injOn_divisors (hfull hx) (hfull hy) hxy
  have hsub : T.image (fun x => x.1*x.2) ⊆
      S.prodPrimes.divisors.filter (fun k => k < C*D) := by
    intro k hk
    obtain ⟨⟨a,d⟩,hp,rfl⟩ := mem_image.mp hk
    have ha := mem_filter.mp (mem_product.mp hp).1
    have hd := mem_filter.mp (mem_product.mp hp).2
    apply mem_filter.mpr
    constructor
    · apply Nat.mem_divisors.mpr
      refine ⟨?_,S.prodPrimes_ne_zero⟩
      have hh := Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors ha.1)
        (Nat.dvd_of_mem_divisors hd.1)
      simpa only [Q,R,sieve_prime_partition] using hh
    · exact (Nat.mul_le_mul_right d ha.2).trans_lt
        (Nat.mul_lt_mul_of_pos_left hd.2 hC)
  have hlow : (∑ d ∈ B, ∑ a ∈ A, |S.rem (a*d)|) ≤
      sieveRemainderBelow S (C*D) := by
    calc
      _ = ∑ x ∈ T, |S.rem (x.1*x.2)| := by rw [sum_comm,sum_product]
      _ = ∑ k ∈ T.image (fun x => x.1*x.2), |S.rem k| :=
        (sum_image (f := fun k => |S.rem k|) hinj).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
  unfold BoundingSieve.errSum
  change (∑ d ∈ R.divisors, |weight d| * |(preSieveCounting S U).rem d|) ≤ _
  calc
    _ = ∑ d ∈ B, |weight d| * |(preSieveCounting S U).rem d| := by
      rw [sum_filter]
      apply sum_congr rfl
      intro d hd
      by_cases hdD : d < D
      · simp only [if_pos hdD]
      · simp only [if_neg hdD,hsupp d (Nat.dvd_of_mem_divisors hd) hdD,abs_zero,zero_mul]
    _ ≤ ∑ d ∈ B, ((∑ a ∈ A, |S.rem (a*d)|) +
        (∑ a ∈ Q.divisors, sqrt (a:ℝ)*|S.rem (a*d)|)/sqrt (C:ℝ)) := by
      apply sum_le_sum
      intro d hd
      have hdR := Nat.dvd_of_mem_divisors (mem_filter.mp hd).1
      exact (le_trans (mul_le_mul_of_nonneg_right (hweight d hdR) (abs_nonneg _))
        (by rw [one_mul])).trans (preSieve_rem_truncated S U hdR hC)
    _ = (∑ d ∈ B, ∑ a ∈ A, |S.rem (a*d)|) +
        (∑ d ∈ B, ∑ a ∈ Q.divisors, sqrt (a:ℝ)*|S.rem (a*d)|)/sqrt (C:ℝ) := by
      rw [sum_add_distrib,sum_div]
    _ ≤ _ := add_le_add hlow le_rfl

#print axioms preSieve_errSum_truncated
#print axioms preSieve_rem_truncated_moments
end ChenEffective.GRH
