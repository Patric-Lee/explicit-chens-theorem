import GRHQuarterMomentFunctions

noncomputable section
namespace ChenEffective.H10Band
open Real Finset ArithmeticFunction
open MathlibNt.SieveTheory.SwitchingPrinciple
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

theorem goldbach_quarter_prime {p : ℕ} (hp : p.Prime) (hp2 : 2<p) :
    quarterRoot (p:ℝ)*AnalyticNumberTheory.Sieve.goldbachNu p≤
      (if p≤100 then (126/100:ℝ) else 101/100)/quarterRoot (p:ℝ)^3+
      (if p=3 then 1/quarterRoot (p:ℝ) else 0) := by
  have hpp : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hr := quarterRoot_pos hpp
  have hfour := quarterRoot_fourth hpp.le
  have hpm : (0:ℝ)<(p:ℝ)-1 := by
    have hpr : (1:ℝ)<p := by exact_mod_cast (by omega : 1<p)
    linarith
  rw [AnalyticNumberTheory.Sieve.goldbachNu_apply_prime hp,mul_one_div]
  by_cases hp3 : p=3
  · subst p
    norm_num only [Nat.cast_ofNat] at hr hfour hpm
    norm_num only [Nat.cast_ofNat,show 3≤100 by norm_num,ite_true]
    have hs : sqrt (3:ℝ)≤2 := (sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
    have hsquare : quarterRoot (3:ℝ)^2=sqrt 3 := sq_sqrt (sqrt_nonneg _)
    have hh : quarterRoot (3:ℝ)/((3:ℝ)-1)≤1/quarterRoot (3:ℝ) := by
      apply (div_le_div_iff₀ (by norm_num) hr).mpr
      nlinarith only [hs,hsquare]
    have hc : (0:ℝ)≤(126/100:ℝ)/quarterRoot (3:ℝ)^3 := by positivity
    linarith only [hh,hc]
  · simp only [if_neg hp3,add_zero]
    apply (div_le_div_iff₀ hpm (pow_pos hr 3)).mpr
    have hp5 : 5≤p := by
      have := hp.eq_two_or_odd
      omega
    split_ifs with hs
    · have hp5r : (5:ℝ)≤p := by exact_mod_cast hp5
      nlinarith only [hfour,hp5r]
    · have hp101 : (101:ℝ)≤p := by exact_mod_cast (show 101≤p by omega)
      nlinarith only [hfour,hp101]

theorem source_quarter_divisor_moments (N : ℕ) :
    let S := jurkatRichertSourceBoundingSieve N
    let Q := ChenEffective.smallSievePrimeProduct S 4000000
    (∑ d∈Q.divisors,1/quarterRoot (d:ℝ)^3)≤exp (1799/100:ℝ) ∧
    (∑ d∈Q.divisors,quarterRoot (d:ℝ)*S.nu d)≤exp (1799/100:ℝ) := by
  let S := jurkatRichertSourceBoundingSieve N
  let Q := ChenEffective.smallSievePrimeProduct S 4000000
  have hQ : Squarefree Q := S.prodPrimes_squarefree.squarefree_of_dvd
    (ChenEffective.smallSievePrimeProduct_dvd S 4000000)
  have hpr : Q.primeFactors=S.prodPrimes.primeFactors.filter
      (fun p : ℕ=>(p:ℝ)<4000000) := by
    apply Nat.primeFactors_prod
    intro p hp
    exact Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
  have hprimes : ∀ p∈Q.primeFactors,2<p ∧ p≤4000000 := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hd := (Nat.dvd_of_mem_primeFactors hp).trans
      (ChenEffective.smallSievePrimeProduct_dvd S 4000000)
    have hlo := (prime_dvd_jurkatRichertSourceSiftingProduct hprime).mp hd |>.1
    have hsize := (mem_filter.mp (hpr ▸ hp)).2
    exact ⟨hlo,by exact_mod_cast hsize.le⟩
  constructor
  · exact reciprocal_quarter_divisor_moment hQ hprimes
  · apply density_quarter_divisor_moment hQ hprimes
      AnalyticNumberTheory.Sieve.goldbachNu AnalyticNumberTheory.Sieve.goldbachNu_isMultiplicative
    · intro p hp
      exact (AnalyticNumberTheory.Sieve.goldbachNu_pos_of_prime (Nat.prime_of_mem_primeFactors hp)).le
    · intro p hp
      exact goldbach_quarter_prime (Nat.prime_of_mem_primeFactors hp) (hprimes p hp).1

#print axioms goldbach_quarter_prime
#print axioms source_quarter_divisor_moments
end ChenEffective.H10Band
end
