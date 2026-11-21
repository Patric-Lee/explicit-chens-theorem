import GRHPrimeRootMoment
import NumericalPreSieveCounting
import MathlibNt.SieveTheory.Switching.SourceSieve

noncomputable section
namespace ChenEffective.GRH
open Real Finset ArithmeticFunction
set_option maxHeartbeats 3000000

def rootArithmeticFunction : ArithmeticFunction ℝ :=
  ⟨fun n => sqrt (n:ℝ),by simp⟩

theorem rootArithmeticFunction_mult : rootArithmeticFunction.IsMultiplicative := by
  constructor
  · norm_num [rootArithmeticFunction]
  · intro m n _
    change sqrt ((m*n:ℕ):ℝ)=sqrt (m:ℝ)*sqrt (n:ℝ)
    rw [Nat.cast_mul,sqrt_mul (Nat.cast_nonneg m)]

def inverseRootArithmeticFunction : ArithmeticFunction ℝ :=
  ⟨fun n => 1/sqrt (n:ℝ),by simp⟩

theorem inverseRootArithmeticFunction_mult : inverseRootArithmeticFunction.IsMultiplicative := by
  constructor
  · norm_num [inverseRootArithmeticFunction]
  · intro m n _
    change 1/sqrt ((m*n:ℕ):ℝ)=(1/sqrt (m:ℝ))*(1/sqrt (n:ℝ))
    rw [Nat.cast_mul,sqrt_mul (Nat.cast_nonneg m),one_div_mul_one_div]

theorem squarefree_divisor_moment_le_exp {Q : ℕ} (hQ : Squarefree Q)
    (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative)
    (hpos : ∀ p ∈ Q.primeFactors, 0 ≤ f p) :
    (∑ d ∈ Q.divisors, f d) ≤ exp (∑ p ∈ Q.primeFactors, f p) := by
  rw [← hf.prodPrimeFactors_one_add_of_squarefree hQ]
  calc
    _ ≤ ∏ p ∈ Q.primeFactors, exp (f p) := by
      apply prod_le_prod₀
      · intro p hp
        linarith only [hpos p hp]
      · intro p _
        linarith only [add_one_le_exp (f p)]
    _ = _ := by rw [exp_sum]

theorem reciprocal_divisor_moment_four_million {Q : ℕ} (hQ : Squarefree Q)
    (hprimes : ∀ p ∈ Q.primeFactors, p ≤ 4000000) :
    (∑ d ∈ Q.divisors, 1/sqrt (d:ℝ)) ≤ exp 1700 := by
  have hh := squarefree_divisor_moment_le_exp hQ inverseRootArithmeticFunction
    inverseRootArithmeticFunction_mult (fun p _ => by
      change 0 ≤ 1/sqrt (p:ℝ)
      positivity)
  change (∑ d ∈ Q.divisors, 1/sqrt (d:ℝ)) ≤
    exp (∑ p ∈ Q.primeFactors, 1/sqrt (p:ℝ)) at hh
  exact hh.trans (exp_le_exp.mpr (prime_root_moment_four_million Q.primeFactors
    (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp,hprimes p hp⟩)))

theorem density_divisor_moment_four_million {Q : ℕ} (hQ : Squarefree Q)
    (hprimes : ∀ p ∈ Q.primeFactors, p ≤ 4000000)
    (v : ArithmeticFunction ℝ) (hv : v.IsMultiplicative)
    (hpos : ∀ p ∈ Q.primeFactors, 0 ≤ v p)
    (hprime : ∀ p ∈ Q.primeFactors,
      sqrt (p:ℝ)*v p ≤ (5/4:ℝ)/sqrt (p:ℝ)+(if p=3 then 1 else 0)) :
    (∑ d ∈ Q.divisors, sqrt (d:ℝ)*v d) ≤ exp 2126 := by
  have hh := squarefree_divisor_moment_le_exp hQ
    (rootArithmeticFunction.pmul v) (rootArithmeticFunction_mult.pmul hv)
    (fun p hp => by
      change 0 ≤ sqrt (p:ℝ)*v p
      exact mul_nonneg (sqrt_nonneg _) (hpos p hp))
  change (∑ d ∈ Q.divisors, sqrt (d:ℝ)*v d) ≤
    exp (∑ p ∈ Q.primeFactors, sqrt (p:ℝ)*v p) at hh
  apply hh.trans
  apply exp_le_exp.mpr
  have hroot := prime_root_moment_four_million Q.primeFactors
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

theorem goldbach_root_prime_bound {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    sqrt (p:ℝ)*AnalyticNumberTheory.Sieve.goldbachNu p ≤
      (5/4:ℝ)/sqrt (p:ℝ)+(if p=3 then 1 else 0) := by
  rw [AnalyticNumberTheory.Sieve.goldbachNu_apply_prime hp]
  by_cases hp3 : p=3
  · subst p
    simp only [Nat.cast_ofNat,sub_self,ite_true]
    have hs : sqrt (3:ℝ) ≤ 2 := by
      exact (sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
    have hn : 0 ≤ (5/4:ℝ)/sqrt 3 := by positivity
    norm_num only [show (3:ℝ)-1=2 by norm_num]
    nlinarith only [hs,hn]
  · have hp5 : 5 ≤ p := by
      by_contra hh
      rcases hp.eq_two_or_odd with h|h <;> omega
    have hpr : (5:ℝ) ≤ p := by exact_mod_cast hp5
    have hs : 0 < sqrt (p:ℝ) := sqrt_pos.2 (by linarith only [hpr])
    have hpm : 0 < (p:ℝ)-1 := by linarith only [hpr]
    simp only [if_neg hp3,add_zero]
    rw [mul_one_div]
    apply (div_le_div_iff₀ hpm hs).mpr
    nlinarith only [sq_sqrt (show 0 ≤ (p:ℝ) by positivity),hpr]

theorem source_small_prime_divisor_moments (N : ℕ) :
    let Q := ChenEffective.smallSievePrimeProduct
      (MathlibNt.SieveTheory.SwitchingPrinciple.jurkatRichertSourceBoundingSieve N) 4000000
    (∑ d ∈ Q.divisors, 1/sqrt (d:ℝ)) ≤ exp 1700 ∧
    (∑ d ∈ Q.divisors, sqrt (d:ℝ)*AnalyticNumberTheory.Sieve.goldbachNu d) ≤ exp 2126 := by
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
  · exact reciprocal_divisor_moment_four_million hQ hsize
  · apply density_divisor_moment_four_million hQ hsize
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

#print axioms source_small_prime_divisor_moments
#print axioms density_divisor_moment_four_million
#print axioms reciprocal_divisor_moment_four_million
end ChenEffective.GRH
