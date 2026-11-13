import BJSSelbergSquareKernel
import BJSSelbergCriticalMass
import BJSSelbergTwoTermIdentity

noncomputable section
namespace ChenEffective
open Real Finset ArithmeticFunction
open MathlibNt.SieveTheory LiuWeight
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem selberg_square_convolution :
    selbergSquareKernel*liuReciprocal=squarefreeReciprocal := by
  apply (IsMultiplicative.eq_iff_eq_on_prime_powers _
    (selberg_square_multiplicative.mul liuReciprocal_isMultiplicative) _
    squarefree_reciprocal_multiplicative).mpr
  intro p k hp
  by_cases hk0 : k=0
  · subst k
    simp [selberg_square_multiplicative.1,liuReciprocal_isMultiplicative.1,
      squarefree_reciprocal_one]
  rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal
    (fun a b => selbergSquareKernel a*liuReciprocal b),Nat.sum_divisors_prime_pow hp]
  have hdiv (j : ℕ) (hj : j≤k) : p^k/p^j=p^(k-j) := by
    apply Nat.div_eq_of_eq_mul_left (pow_pos hp.pos j)
    rw [← pow_add,Nat.sub_add_cancel hj]
  have hpr (j : ℕ) : liuReciprocal (p^j)=1/(p:ℝ)^j := by
    simp [liuReciprocal,hp.ne_zero]
  have hloc (j : ℕ) (hj : j<k+1) :
      selbergSquareKernel (p^j)*liuReciprocal (p^k/p^j)=
      selbergSquareLocal p j*(1/(p:ℝ)^(k-j)) := by
    rw [selberg_square_prime_pow hp,hdiv j (by omega),hpr]
  rw [sum_congr rfl (fun j hj => hloc j (mem_range.mp hj))]
  by_cases hk : k=1
  · subst k
    simp [Finset.sum_range_succ,selbergSquareLocal,squarefree_reciprocal_prime p hp]
  · have hk2 : 2≤k := by omega
    rw [squarefree_reciprocal_prime_pow hp hk2]
    have hshort : (∑ j∈range (k+1),selbergSquareLocal p j*(1/(p:ℝ)^(k-j)))=
        ∑ j∈({0,2}:Finset ℕ),selbergSquareLocal p j*(1/(p:ℝ)^(k-j)) := by
      symm
      apply sum_subset
      · intro j hj
        simp only [mem_insert,mem_singleton] at hj
        rcases hj with rfl|rfl
        · exact mem_range.mpr (by omega)
        · exact mem_range.mpr (by omega)
      · intro j hj hnot
        simp only [mem_insert,mem_singleton,not_or] at hnot
        simp [selbergSquareLocal,hnot.1,hnot.2]
    rw [hshort]
    norm_num only [sum_insert (by decide : (0:ℕ)∉({2}:Finset ℕ)),sum_singleton,
      selbergSquareLocal,Nat.sub_zero,reduceIte,if_true,if_false,one_mul]
    have hp0 : (p:ℝ)≠0 := by exact_mod_cast hp.ne_zero
    have he : (p:ℝ)^k=(p:ℝ)^2*(p:ℝ)^(k-2) := by rw [← pow_add,Nat.add_sub_of_le hk2]
    rw [he]
    field_simp
    ring

theorem selberg_correction_square_convolution {N : ℕ} (hEven : Even N) :
    liuSelbergCorrection N=selbergSquareKernel*selbergCriticalCorrection N := by
  unfold liuSelbergCorrection
  rw [← selberg_critical_convolution hEven,← selberg_square_convolution]
  calc
    _ = (liuMoebiusReciprocal*liuReciprocal)*
        (selbergSquareKernel*selbergCriticalCorrection N) := by ring
    _ = _ := by rw [mul_comm liuMoebiusReciprocal liuReciprocal,
      liuReciprocal_mul_liuMoebiusReciprocal,one_mul]

end ChenEffective
