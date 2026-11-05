import NumericalPreSieveCounting

namespace ChenEffective
open Real Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.LinearSieve
open scoped Classical ArithmeticFunction.Moebius
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

noncomputable def sieveRemainderBelow (S : BoundingSieve) (L : ℕ) : ℝ :=
  ∑ d ∈ S.prodPrimes.divisors.filter (fun d => d < L), |S.rem d|

theorem preSieveCounting_rem_abs (S : BoundingSieve) (U : ℝ) {d : ℕ}
    (hd : d ∣ restrictedSievePrimeProduct S U) :
    |(preSieveCounting S U).rem d| ≤
      ∑ a ∈ (smallSievePrimeProduct S U).divisors, |S.rem (a * d)| := by
  rw [preSieveCounting_rem S U hd]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro a ha
  rw [abs_mul]
  have hmu : |(μ a : ℝ)| ≤ 1 := by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := a))
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hmu (abs_nonneg (S.rem (a * d)))

/-- The QD remainder has no multiplicity factor: coprimality makes each
small-prime/large-prime divisor pair give a distinct original discrepancy. -/
theorem preSieveCounting_errSum_QD (S : BoundingSieve) (U : ℝ) (D : ℕ) (weight : ℕ → ℝ)
    (hsupp : ∀ d : ℕ, d ∣ restrictedSievePrimeProduct S U → ¬d < D → weight d = 0)
    (hweight : ∀ d : ℕ, d ∣ restrictedSievePrimeProduct S U → |weight d| ≤ 1) :
    (preSieveCounting S U).errSum weight ≤ sieveRemainderBelow S (smallSievePrimeProduct S U * D) := by
  let Q := smallSievePrimeProduct S U
  let R := restrictedSievePrimeProduct S U
  let T := Q.divisors ×ˢ (R.divisors.filter (fun d => d < D))
  have hcop : Q.Coprime R := sieve_prime_partition_coprime S U
  have hQ : 0 < Q := by
    have hdiv := smallSievePrimeProduct_dvd S U
    change Q ∣ S.prodPrimes at hdiv
    by_contra hh
    have hz : Q = 0 := by omega
    rw [hz] at hdiv
    exact S.prodPrimes_ne_zero (zero_dvd_iff.mp hdiv)
  have hfull : T ⊆ Q.divisors ×ˢ R.divisors := by
    intro x hx
    exact mem_product.mpr ⟨(mem_product.mp hx).1, (mem_filter.mp (mem_product.mp hx).2).1⟩
  have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2) (↑T : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    exact hcop.mul_injOn_divisors (hfull hx) (hfull hy) hxy
  have hsub : T.image (fun x => x.1 * x.2) ⊆
      S.prodPrimes.divisors.filter (fun d => d < Q * D) := by
    intro k hk
    obtain ⟨⟨a,d⟩, hp, rfl⟩ := mem_image.mp hk
    have ha := Nat.mem_divisors.mp (mem_product.mp hp).1
    have hd := Nat.mem_divisors.mp (mem_filter.mp (mem_product.mp hp).2).1
    have hdD := (mem_filter.mp (mem_product.mp hp).2).2
    apply mem_filter.mpr
    constructor
    · apply Nat.mem_divisors.mpr
      refine ⟨?_, S.prodPrimes_ne_zero⟩
      have hh := Nat.mul_dvd_mul ha.1 hd.1
      simpa only [Q, R, sieve_prime_partition] using hh
    · have haQ : a ≤ Q := Nat.le_of_dvd hQ ha.1
      exact (Nat.mul_le_mul_right d haQ).trans_lt (Nat.mul_lt_mul_of_pos_left hdD hQ)
  have hmap : (∑ k ∈ T.image (fun x => x.1 * x.2), |S.rem k|) =
      ∑ x ∈ T, |S.rem (x.1 * x.2)| := Finset.sum_image hinj
  unfold BoundingSieve.errSum
  change (∑ d ∈ R.divisors, |weight d| * |(preSieveCounting S U).rem d|) ≤ _
  calc
    _ = ∑ d ∈ R.divisors.filter (fun d => d < D), |weight d| * |(preSieveCounting S U).rem d| := by
      rw [sum_filter]
      apply sum_congr rfl
      intro d hd
      by_cases hdD : d < D
      · simp only [if_pos hdD]
      · simp only [if_neg hdD, hsupp d (Nat.mem_divisors.mp hd).1 hdD, abs_zero, zero_mul]
    _ ≤ ∑ d ∈ R.divisors.filter (fun d => d < D),
        ∑ a ∈ Q.divisors, |S.rem (a * d)| := by
      apply sum_le_sum
      intro d hd
      have hdR := (Nat.mem_divisors.mp (mem_filter.mp hd).1).1
      apply le_trans (show |weight d| * |(preSieveCounting S U).rem d| ≤ |(preSieveCounting S U).rem d| from
        (mul_le_mul_of_nonneg_right (hweight d hdR) (abs_nonneg _)).trans_eq (one_mul _))
      exact preSieveCounting_rem_abs S U hdR
    _ = ∑ x ∈ T, |S.rem (x.1 * x.2)| := by rw [sum_comm, sum_product]
    _ = ∑ k ∈ T.image (fun x => x.1 * x.2), |S.rem k| := hmap.symm
    _ ≤ sieveRemainderBelow S (Q * D) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)

#print axioms preSieveCounting_errSum_QD
end ChenEffective
