import BJSSelbergSpecialization
import NumericalSelbergEulerMajorant

/-! Removing the square-Moebius kernel leaves a correction whose absolute
square-root moment converges. Its dependence on prime divisors of N is
retained, rather than hidden in a constant depending on N. -/
noncomputable section
namespace ChenEffective
open Real Finset ArithmeticFunction
open MathlibNt.SieveTheory LiuWeight
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def primePowerExtension (F : ℕ → ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n=0 then 0 else n.factorization.prod F,by simp⟩

theorem primePowerExtension_multiplicative (F : ℕ → ℕ → ℝ) :
    (primePowerExtension F).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  constructor
  · simp [primePowerExtension]
  · intro m n hm hn hmn
    simp only [primePowerExtension,ArithmeticFunction.coe_mk,if_neg hm,if_neg hn,
      if_neg (mul_ne_zero hm hn),Nat.factorization_mul_of_coprime hmn]
    exact Finsupp.prod_add_index_of_disjoint hmn.disjoint_primeFactors F

theorem primePowerExtension_prime_pow (F : ℕ → ℕ → ℝ)
    (hF : ∀ p, F p 0=1) {p k : ℕ} (hp : p.Prime) :
    primePowerExtension F (p^k)=F p k := by
  simp only [primePowerExtension,ArithmeticFunction.coe_mk,
    if_neg (pow_ne_zero k hp.ne_zero),hp.factorization_pow]
  simp [Finsupp.prod_single_index,hF]

def selbergCriticalLocal (N p k : ℕ) : ℝ :=
  if k=0 then 1 else
  if p∣N then (-1/(p:ℝ))^k else
    (2/((p:ℝ)-2))*(-1:ℝ)^(k-1)/(p:ℝ)^k

def selbergCriticalCorrection (N : ℕ) : ArithmeticFunction ℝ :=
  primePowerExtension (selbergCriticalLocal N)

theorem selberg_critical_multiplicative (N : ℕ) :
    (selbergCriticalCorrection N).IsMultiplicative :=
  primePowerExtension_multiplicative _

theorem selberg_critical_prime_pow {N p k : ℕ} (hp : p.Prime) :
    selbergCriticalCorrection N (p^k)=selbergCriticalLocal N p k :=
  primePowerExtension_prime_pow _ (by intro p; simp [selbergCriticalLocal]) hp

def squarefreeReciprocal : ArithmeticFunction ℝ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℝ).ppow 2 |>.pdiv ArithmeticFunction.id

theorem squarefree_reciprocal_multiplicative : squarefreeReciprocal.IsMultiplicative := by
  exact (ArithmeticFunction.isMultiplicative_moebius.intCast.ppow).pdiv
    ArithmeticFunction.isMultiplicative_id.natCast

theorem squarefree_reciprocal_prime (p : ℕ) (hp : p.Prime) :
    squarefreeReciprocal p=1/(p:ℝ) := by
  simp [squarefreeReciprocal,ArithmeticFunction.pdiv_apply,
    ArithmeticFunction.ppow_apply (by norm_num : 0<2),
    ArithmeticFunction.moebius_apply_prime hp,ArithmeticFunction.id_apply]

theorem squarefree_reciprocal_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 2≤k) :
    squarefreeReciprocal (p^k)=0 := by
  simp [squarefreeReciprocal,ArithmeticFunction.pdiv_apply,
    ArithmeticFunction.ppow_apply (by norm_num : 0<2),
    ArithmeticFunction.moebius_apply_prime_pow hp (by omega : k≠0),
    show k≠1 by omega]

theorem squarefree_reciprocal_one : squarefreeReciprocal 1=1 :=
  squarefree_reciprocal_multiplicative.1

theorem selberg_critical_convolution_prime {N p k : ℕ} (hp : p.Prime) (hk : 1≤k) :
    (squarefreeReciprocal*selbergCriticalCorrection N) (p^k) =
      selbergCriticalLocal N p k + selbergCriticalLocal N p (k-1)/(p:ℝ) := by
  rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal
    (fun a b => squarefreeReciprocal a*selbergCriticalCorrection N b),
    Nat.sum_divisors_prime_pow hp]
  have hdiv (j : ℕ) (hj : j≤k) : p^k/p^j=p^(k-j) := by
    apply Nat.div_eq_of_eq_mul_left (pow_pos hp.pos j)
    rw [← pow_add,Nat.sub_add_cancel hj]
  have hshort : (∑ j∈range (k+1), squarefreeReciprocal (p^j)*
      selbergCriticalCorrection N (p^k/p^j)) =
      ∑ j∈({0,1}:Finset ℕ),squarefreeReciprocal (p^j)*
        selbergCriticalCorrection N (p^k/p^j) := by
    symm
    apply Finset.sum_subset
    · intro j hj
      simp only [mem_insert,mem_singleton] at hj
      rcases hj with rfl|rfl
      · exact mem_range.mpr (by omega)
      · exact mem_range.mpr (by omega)
    · intro j hj hj01
      have hj2 : 2≤j := by simp only [mem_insert,mem_singleton,not_or] at hj01; omega
      rw [squarefree_reciprocal_prime_pow hp hj2,zero_mul]
  rw [hshort]
  simp only [sum_insert (by decide : (0:ℕ)∉({1}:Finset ℕ)),sum_singleton,
    pow_zero,pow_one,squarefree_reciprocal_one,one_mul,
    squarefree_reciprocal_prime p hp]
  rw [Nat.div_one,show p^k/p=p^(k-1) by simpa only [pow_one] using hdiv 1 hk]
  simp only [selberg_critical_prime_pow hp]
  ring

theorem selberg_critical_convolution {N : ℕ} (hEven : Even N) :
    squarefreeReciprocal*selbergCriticalCorrection N=liuSelbergArithmeticFunction N := by
  apply (IsMultiplicative.eq_iff_eq_on_prime_powers _
    (squarefree_reciprocal_multiplicative.mul (selberg_critical_multiplicative N)) _
    (liuSelbergArithmeticFunction_isMultiplicative N)).mpr
  intro p k hp
  by_cases hk0 : k=0
  · subst k
    simp [squarefree_reciprocal_one,selbergCriticalCorrection,primePowerExtension,
      liuSelbergArithmeticFunction_apply]
  have hk1 : 1≤k := by omega
  rw [selberg_critical_convolution_prime hp hk1]
  by_cases hpd : p∣N
  · have hsf : liuSelbergArithmeticFunction N (p^k)=0 := by
      rw [liuSelbergArithmeticFunction_apply]
      apply liuSelbergArithmetic_eq_zero_of_not_squarefree_or_not_coprime
      intro hh
      exact (hp.coprime_iff_not_dvd.mp
        (Nat.Coprime.of_dvd_left (dvd_pow_self p hk0) hh.2)) hpd
    rw [hsf]
    by_cases hk : k=1
    · subst k; simp [selbergCriticalLocal,hpd]; ring
    have hk2 : 2≤k := by omega
    simp only [selbergCriticalLocal,if_neg hk0,if_pos hpd,if_neg (show k-1≠0 by omega)]
    have he : k=(k-1)+1 := by omega
    nth_rw 1 [he]
    rw [pow_succ]
    ring
  · have hp2 : 2<p := by
      have hpne : p≠2 := by intro hh; subst p; exact hpd hEven.two_dvd
      have := hp.two_le
      omega
    have hp0R : (p:ℝ)≠0 := by exact_mod_cast hp.ne_zero
    have hp2R : (p:ℝ)-2≠0 := by
      have hpR : (2:ℝ)<p := by exact_mod_cast hp2
      linarith
    by_cases hk : k=1
    · subst k
      rw [liuSelbergArithmeticFunction_apply,pow_one,liuSelbergArithmetic_eq_prod hp.ne_zero
        hp.squarefree (hp.coprime_iff_not_dvd.mpr hpd)]
      simp [selbergCriticalLocal,hpd,hp.primeFactors]
      field_simp
      ring
    have hk2 : 2≤k := by omega
    have hsf : liuSelbergArithmeticFunction N (p^k)=0 := by
      rw [liuSelbergArithmeticFunction_apply]
      apply liuSelbergArithmetic_eq_zero_of_not_squarefree_or_not_coprime
      intro hh
      have hbad : ¬Squarefree (p^k) := by
        rw [Nat.squarefree_pow_iff hp.ne_one hk0]
        simp [hk]
      exact hbad hh.1
    rw [hsf]
    simp only [selbergCriticalLocal,if_neg hk0,if_neg hpd,if_neg (show k-1≠0 by omega)]
    have he1 : k=(k-1)+1 := by omega
    have he2 : k-1=(k-1-1)+1 := by omega
    rw [show (p:ℝ)^k=(p:ℝ)^(k-1)*p by rw [← pow_succ,← he1]]
    rw [show (-1:ℝ)^(k-1)=(-1:ℝ)^(k-1-1)*(-1) by rw [← pow_succ,← he2]]
    field_simp
    ring

end ChenEffective
