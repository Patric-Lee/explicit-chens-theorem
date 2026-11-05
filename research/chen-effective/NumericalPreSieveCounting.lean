import NumericalPresievedSourceLayers
import Mathlib.Data.Finset.NatDivisors

namespace ChenEffective
open Real Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.LinearSieve
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

noncomputable def smallSievePrimeProduct (S : BoundingSieve) (U : ℝ) : ℕ :=
  ∏ p ∈ S.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < U), p

theorem sieve_prime_partition (S : BoundingSieve) (U : ℝ) :
    smallSievePrimeProduct S U * restrictedSievePrimeProduct S U = S.prodPrimes := by
  unfold smallSievePrimeProduct restrictedSievePrimeProduct
  have hh := Finset.prod_filter_mul_prod_filter_not S.prodPrimes.primeFactors
    (fun p : ℕ => (p : ℝ) < U) (fun p => p)
  simpa only [not_lt] using hh.trans (Nat.prod_primeFactors_of_squarefree S.prodPrimes_squarefree)

theorem smallSievePrimeProduct_dvd (S : BoundingSieve) (U : ℝ) :
    smallSievePrimeProduct S U ∣ S.prodPrimes := by
  rw [← sieve_prime_partition S U]
  exact dvd_mul_right _ _

theorem sieve_prime_partition_coprime (S : BoundingSieve) (U : ℝ) :
    Nat.Coprime (smallSievePrimeProduct S U) (restrictedSievePrimeProduct S U) := by
  unfold smallSievePrimeProduct restrictedSievePrimeProduct
  apply Nat.coprime_prod_left_iff.mpr
  intro p hp
  apply Nat.coprime_prod_right_iff.mpr
  intro q hq
  have hpP := (mem_filter.mp hp).1
  have hqP := (mem_filter.mp hq).1
  apply (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hpP)
    (Nat.prime_of_mem_primeFactors hqP)).mpr
  intro heq
  have hpU := (mem_filter.mp hp).2
  have hqU := (mem_filter.mp hq).2
  rw [heq] at hpU
  linarith

noncomputable def smallSieveEuler (S : BoundingSieve) (U : ℝ) : ℝ :=
  ∏ p ∈ (smallSievePrimeProduct S U).primeFactors, (1 - S.nu p)

noncomputable def preSieveCounting (S : BoundingSieve) (U : ℝ) : BoundingSieve :=
  { restrictSievePrimes S U with
    weights := fun n => if Nat.Coprime (smallSievePrimeProduct S U) n then S.weights n else 0
    weights_nonneg := by intro n; split_ifs <;> positivity
    totalMass := S.totalMass * smallSieveEuler S U }

theorem preSieveCounting_siftedSum (S : BoundingSieve) (U : ℝ) :
    (preSieveCounting S U).siftedSum = S.siftedSum := by
  unfold BoundingSieve.siftedSum
  change (∑ n ∈ S.support, if Nat.Coprime (restrictedSievePrimeProduct S U) n then
    (if Nat.Coprime (smallSievePrimeProduct S U) n then S.weights n else 0) else 0) = _
  rw [← sieve_prime_partition S U]
  apply sum_congr rfl
  intro n hn
  simp only [Nat.coprime_mul_iff_left]
  split_ifs <;> simp_all

theorem sum_real_moebius (n : ℕ) :
    (∑ a ∈ n.divisors, (μ a : ℝ)) = if n = 1 then 1 else 0 := by
  have hh := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply,
    ArithmeticFunction.intCoe_apply] using hh

theorem coprime_indicator_moebius (Q n : ℕ) (hQ : Q ≠ 0) :
    (if Nat.Coprime Q n then (1 : ℝ) else 0) =
      ∑ a ∈ Q.divisors, if a ∣ n then (μ a : ℝ) else 0 := by
  have hg : Nat.gcd Q n ≠ 0 := by
    intro hz
    have hh := Nat.gcd_eq_zero_iff.mp hz
    exact hQ hh.1
  have hd : Q.divisors.filter (fun a => a ∣ n) = (Nat.gcd Q n).divisors := by
    ext a
    constructor
    · intro ha
      exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd (Nat.mem_divisors.mp (mem_filter.mp ha).1).1
        (mem_filter.mp ha).2, hg⟩
    · intro ha
      have hh := Nat.dvd_gcd_iff.mp (Nat.mem_divisors.mp ha).1
      exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hh.1, hQ⟩, hh.2⟩
  rw [← sum_filter, hd, sum_real_moebius]

theorem smallSieveEuler_moebius (S : BoundingSieve) (U : ℝ) :
    smallSieveEuler S U = ∑ a ∈ (smallSievePrimeProduct S U).divisors, (μ a : ℝ) * S.nu a := by
  have hsq := S.prodPrimes_squarefree.squarefree_of_dvd (smallSievePrimeProduct_dvd S U)
  simpa only [smallSieveEuler, ArithmeticFunction.intCoe_apply] using
    S.nu_mult.prodPrimeFactors_one_sub_of_squarefree S.nu hsq

/-- Exact divisibility-count identity for the pre-sieved sequence. -/
theorem preSieveCounting_multSum (S : BoundingSieve) (U : ℝ) {d : ℕ}
    (hd : d ∣ restrictedSievePrimeProduct S U) :
    (preSieveCounting S U).multSum d =
      ∑ a ∈ (smallSievePrimeProduct S U).divisors, (μ a : ℝ) * S.multSum (a * d) := by
  let Q := smallSievePrimeProduct S U
  have hQ : Q ≠ 0 := by
    intro hz
    have hh := smallSievePrimeProduct_dvd S U
    change Q ∣ S.prodPrimes at hh
    rw [hz] at hh
    exact S.prodPrimes_ne_zero (zero_dvd_iff.mp hh)
  have hcop : Nat.Coprime Q d := (sieve_prime_partition_coprime S U).of_dvd_right hd
  unfold BoundingSieve.multSum
  change (∑ n ∈ S.support, if d ∣ n then (if Nat.Coprime Q n then S.weights n else 0) else 0) = _
  have hweights (n : ℕ) : (if Nat.Coprime Q n then S.weights n else 0) =
      S.weights n * ∑ a ∈ Q.divisors, if a ∣ n then (μ a : ℝ) else 0 := by
    rw [← coprime_indicator_moebius Q n hQ]
    split_ifs <;> simp
  simp_rw [hweights, Finset.mul_sum]
  have hswap : (∑ n ∈ S.support, if d ∣ n then
      ∑ a ∈ Q.divisors, S.weights n * (if a ∣ n then (μ a : ℝ) else 0) else 0) =
      ∑ n ∈ S.support, ∑ a ∈ Q.divisors,
        if d ∣ n then S.weights n * (if a ∣ n then (μ a : ℝ) else 0) else 0 := by
    apply sum_congr rfl
    intro n hn
    split_ifs <;> simp
  rw [hswap, Finset.sum_comm]
  apply sum_congr rfl
  intro a ha
  have had : Nat.Coprime a d := hcop.of_dvd_left (Nat.mem_divisors.mp ha).1
  apply sum_congr rfl
  intro n hn
  by_cases hdn : d ∣ n
  · by_cases han : a ∣ n
    · have hprod : a * d ∣ n := had.mul_dvd_of_dvd_of_dvd han hdn
      simp [hdn, han, hprod]
      ring
    · have hprod : ¬a * d ∣ n := fun h => han ((dvd_mul_right a d).trans h)
      simp [hdn, han, hprod]
  · have hprod : ¬a * d ∣ n := fun h => hdn ((dvd_mul_left d a).trans h)
    simp [hdn, hprod]

theorem preSieveCounting_rem (S : BoundingSieve) (U : ℝ) {d : ℕ}
    (hd : d ∣ restrictedSievePrimeProduct S U) :
    (preSieveCounting S U).rem d =
      ∑ a ∈ (smallSievePrimeProduct S U).divisors, (μ a : ℝ) * S.rem (a * d) := by
  have hcop := (sieve_prime_partition_coprime S U).of_dvd_right hd
  rw [BoundingSieve.rem, preSieveCounting_multSum S U hd]
  change _ - S.nu d * (S.totalMass * smallSieveEuler S U) = _
  rw [smallSieveEuler_moebius, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply sum_congr rfl
  intro a ha
  rw [BoundingSieve.rem, S.nu_mult.map_mul_of_coprime (hcop.of_dvd_left (Nat.mem_divisors.mp ha).1)]
  ring

#print axioms preSieveCounting_siftedSum
#print axioms preSieveCounting_rem
end ChenEffective
