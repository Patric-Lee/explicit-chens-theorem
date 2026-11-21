import GRHDivisorMoments
import GRHSharpRootMoment

noncomputable section
namespace ChenEffective.GRH
open Real Finset ArithmeticFunction
set_option maxHeartbeats 3000000

theorem reciprocal_divisor_moment_four_million_sharp {Q : ℕ} (hQ : Squarefree Q)
    (hprimes : ∀ p ∈ Q.primeFactors, p ≤ 4000000) :
    (∑ d ∈ Q.divisors, 1/sqrt (d:ℝ)) ≤ exp 1173 := by
  have hh := squarefree_divisor_moment_le_exp hQ inverseRootArithmeticFunction
    inverseRootArithmeticFunction_mult (fun p _ => by
      change 0 ≤ 1/sqrt (p:ℝ)
      positivity)
  change (∑ d ∈ Q.divisors, 1/sqrt (d:ℝ)) ≤
    exp (∑ p ∈ Q.primeFactors, 1/sqrt (p:ℝ)) at hh
  exact hh.trans (exp_le_exp.mpr (prime_root_moment_four_million_sharp Q.primeFactors
    (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp,hprimes p hp⟩)))

theorem density_divisor_moment_four_million_sharp {Q : ℕ} (hQ : Squarefree Q)
    (hprimes : ∀ p ∈ Q.primeFactors, p ≤ 4000000)
    (v : ArithmeticFunction ℝ) (hv : v.IsMultiplicative)
    (hpos : ∀ p ∈ Q.primeFactors, 0 ≤ v p)
    (hprime : ∀ p ∈ Q.primeFactors,
      sqrt (p:ℝ)*v p ≤ (5/4:ℝ)/sqrt (p:ℝ)+(if p=3 then 1 else 0)) :
    (∑ d ∈ Q.divisors, sqrt (d:ℝ)*v d) ≤ exp 1468 := by
  have hh := squarefree_divisor_moment_le_exp hQ
    (rootArithmeticFunction.pmul v) (rootArithmeticFunction_mult.pmul hv)
    (fun p hp => by
      change 0 ≤ sqrt (p:ℝ)*v p
      exact mul_nonneg (sqrt_nonneg _) (hpos p hp))
  change (∑ d ∈ Q.divisors, sqrt (d:ℝ)*v d) ≤
    exp (∑ p ∈ Q.primeFactors, sqrt (p:ℝ)*v p) at hh
  apply hh.trans
  apply exp_le_exp.mpr
  have hroot := prime_root_moment_four_million_sharp Q.primeFactors
    (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp,hprimes p hp⟩)
  have hsum := sum_le_sum hprime
  have heq : (∑ p ∈ Q.primeFactors, (5/4:ℝ)/sqrt (p:ℝ)) =
      (5/4:ℝ)*(∑ p ∈ Q.primeFactors, 1/sqrt (p:ℝ)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    ring
  have hind : (∑ p ∈ Q.primeFactors, if p=3 then (1:ℝ) else 0) ≤ 1 := by
    simp only [sum_ite_eq']
    split_ifs <;> norm_num
  rw [sum_add_distrib,heq] at hsum
  linarith only [hsum,hroot,hind]

theorem source_small_prime_divisor_moments_sharp (N : ℕ) :
    let Q := ChenEffective.smallSievePrimeProduct
      (MathlibNt.SieveTheory.SwitchingPrinciple.jurkatRichertSourceBoundingSieve N) 4000000
    (∑ d ∈ Q.divisors, 1/sqrt (d:ℝ)) ≤ exp 1173 ∧
    (∑ d ∈ Q.divisors, sqrt (d:ℝ)*AnalyticNumberTheory.Sieve.goldbachNu d) ≤ exp 1468 := by
  let S := MathlibNt.SieveTheory.SwitchingPrinciple.jurkatRichertSourceBoundingSieve N
  let Q := ChenEffective.smallSievePrimeProduct S 4000000
  have hQ : Squarefree Q :=
    S.prodPrimes_squarefree.squarefree_of_dvd (ChenEffective.smallSievePrimeProduct_dvd S 4000000)
  have hpr : Q.primeFactors = S.prodPrimes.primeFactors.filter
      (fun p : ℕ => (p:ℝ) < 4000000) := by
    apply Nat.primeFactors_prod
    intro p hp
    exact Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
  have hsize : ∀ p ∈ Q.primeFactors, p ≤ 4000000 := by
    intro p hp
    rw [hpr] at hp
    have hh := (mem_filter.mp hp).2
    exact_mod_cast hh.le
  constructor
  · exact reciprocal_divisor_moment_four_million_sharp hQ hsize
  · apply density_divisor_moment_four_million_sharp hQ hsize
      AnalyticNumberTheory.Sieve.goldbachNu AnalyticNumberTheory.Sieve.goldbachNu_isMultiplicative
    · intro p hp
      exact (AnalyticNumberTheory.Sieve.goldbachNu_pos_of_prime
        (Nat.prime_of_mem_primeFactors hp)).le
    · intro p hp
      apply goldbach_root_prime_bound (Nat.prime_of_mem_primeFactors hp)
      have hd := (Nat.dvd_of_mem_primeFactors hp).trans
        (ChenEffective.smallSievePrimeProduct_dvd S 4000000)
      exact (MathlibNt.SieveTheory.SwitchingPrinciple.prime_dvd_jurkatRichertSourceSiftingProduct
        (Nat.prime_of_mem_primeFactors hp)).mp hd |>.1


#print axioms source_small_prime_divisor_moments_sharp
#print axioms density_divisor_moment_four_million_sharp
end ChenEffective.GRH
