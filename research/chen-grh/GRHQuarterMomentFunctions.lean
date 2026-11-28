import GRHQuarterPrimeEnvelope
import GRHH10Rankin

noncomputable section
namespace ChenEffective.H10Band
open Real Finset ArithmeticFunction
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

theorem quarterRoot_mul {x y : ℝ} (hx : 0≤x) :
    quarterRoot (x*y)=quarterRoot x*quarterRoot y := by
  unfold quarterRoot
  rw [sqrt_mul hx,sqrt_mul (sqrt_nonneg x)]

theorem quarterRoot_rpow {x : ℝ} (hx : 0≤x) : quarterRoot x=x^(1/4:ℝ) := by
  unfold quarterRoot
  rw [sqrt_eq_rpow,sqrt_eq_rpow,←rpow_mul hx]
  norm_num

theorem quarterRoot_div_self {x : ℝ} (hx : 0≤x) :
    quarterRoot x/x=1/quarterRoot x^3 := by
  by_cases hzero : x=0
  · subst x;simp [quarterRoot]
  have hr := quarterRoot_pos (lt_of_le_of_ne hx (Ne.symm hzero))
  have hfour := quarterRoot_fourth hx
  apply (div_eq_div_iff hzero (ne_of_gt (pow_pos hr 3))).mpr
  nlinarith only [hfour]

def quarterArithmeticFunction : ArithmeticFunction ℝ :=
  ⟨fun n=>quarterRoot (n:ℝ),by simp [quarterRoot]⟩

theorem quarterArithmeticFunction_mult : quarterArithmeticFunction.IsMultiplicative := by
  constructor
  · norm_num [quarterArithmeticFunction,quarterRoot]
  · intro m n _
    change quarterRoot ((m*n:ℕ):ℝ)=quarterRoot (m:ℝ)*quarterRoot (n:ℝ)
    rw [Nat.cast_mul,quarterRoot_mul (Nat.cast_nonneg m)]

def inverseQuarterCube : ArithmeticFunction ℝ :=
  ⟨fun n=>1/quarterRoot (n:ℝ)^3,by simp [quarterRoot]⟩

theorem inverseQuarterCube_mult : inverseQuarterCube.IsMultiplicative := by
  constructor
  · norm_num [inverseQuarterCube,quarterRoot]
  · intro m n _
    change 1/quarterRoot ((m*n:ℕ):ℝ)^3=
      (1/quarterRoot (m:ℝ)^3)*(1/quarterRoot (n:ℝ)^3)
    rw [Nat.cast_mul,quarterRoot_mul (Nat.cast_nonneg m),mul_pow,one_div_mul_one_div]

theorem reciprocal_quarter_prime_log {p : ℕ} (hp : 2<p) :
    Real.log (1+1/quarterRoot (p:ℝ)^3)≤primeEnvelope p := by
  have hq : 0<quarterRoot (p:ℝ) := quarterRoot_pos (by exact_mod_cast (by omega : 0<p))
  have hc : (1:ℝ)≤ if p≤100 then 126/100 else 101/100 := by split_ifs <;> norm_num
  have hi := div_le_div_of_nonneg_right hc (pow_nonneg hq.le 3)
  have hs : (0:ℝ)≤ if p=3 then 1/quarterRoot (p:ℝ) else 0 := by split_ifs <;> positivity
  unfold primeEnvelope
  apply Real.log_le_log (by positivity)
  linarith only [hi,hs]

/-- Certified Rankin moment for the counting part, with exponent 1/4. -/
theorem reciprocal_quarter_divisor_moment {Q : ℕ} (hQ : Squarefree Q)
    (hprimes : ∀ p∈Q.primeFactors,2<p ∧ p≤4000000) :
    (∑ d∈Q.divisors,1/quarterRoot (d:ℝ)^3)≤exp (1799/100:ℝ) := by
  have he := squarefree_divisor_moment_exact_log hQ inverseQuarterCube
    inverseQuarterCube_mult (fun p _ => by
      change 0≤1/quarterRoot (p:ℝ)^3
      exact div_nonneg (by norm_num) (pow_nonneg (quarterRoot_nonneg _) _))
  change (∑ d∈Q.divisors,1/quarterRoot (d:ℝ)^3)=
    exp (∑ p∈Q.primeFactors,Real.log (1+1/quarterRoot (p:ℝ)^3)) at he
  rw [he]
  apply exp_le_exp.mpr
  exact (sum_le_sum (fun p hp=>reciprocal_quarter_prime_log (hprimes p hp).1)).trans
    (quarter_prime_envelope_cap Q.primeFactors
      (fun p hp=>⟨Nat.prime_of_mem_primeFactors hp,hprimes p hp⟩))

/-- The same certificate controls any multiplicative density below its envelope. -/
theorem density_quarter_divisor_moment {Q : ℕ} (hQ : Squarefree Q)
    (hprimes : ∀ p∈Q.primeFactors,2<p ∧ p≤4000000)
    (v : ArithmeticFunction ℝ) (hv : v.IsMultiplicative)
    (hpos : ∀ p∈Q.primeFactors,0≤v p)
    (hprime : ∀ p∈Q.primeFactors,
      quarterRoot (p:ℝ)*v p≤
        (if p≤100 then (126/100:ℝ) else 101/100)/quarterRoot (p:ℝ)^3+
        (if p=3 then 1/quarterRoot (p:ℝ) else 0)) :
    (∑ d∈Q.divisors,quarterRoot (d:ℝ)*v d)≤exp (1799/100:ℝ) := by
  have he := squarefree_divisor_moment_exact_log hQ
    (quarterArithmeticFunction.pmul v) (quarterArithmeticFunction_mult.pmul hv)
    (fun p hp => by
      change 0≤quarterRoot (p:ℝ)*v p
      exact mul_nonneg (quarterRoot_nonneg _) (hpos p hp))
  change (∑ d∈Q.divisors,quarterRoot (d:ℝ)*v d)=
    exp (∑ p∈Q.primeFactors,Real.log (1+quarterRoot (p:ℝ)*v p)) at he
  rw [he]
  apply exp_le_exp.mpr
  have hh : (∑ p∈Q.primeFactors,Real.log (1+quarterRoot (p:ℝ)*v p))≤
      ∑ p∈Q.primeFactors,primeEnvelope p := by
    apply sum_le_sum
    intro p hp
    have h := Real.log_le_log (by
      have := mul_nonneg (quarterRoot_nonneg (p:ℝ)) (hpos p hp)
      linarith)
      (add_le_add_left (hprime p hp) 1)
    simpa only [primeEnvelope,add_comm,add_left_comm,add_assoc] using h
  apply hh.trans
  exact quarter_prime_envelope_cap Q.primeFactors
    (fun p hp=>⟨Nat.prime_of_mem_primeFactors hp,hprimes p hp⟩)

#print axioms reciprocal_quarter_divisor_moment
#print axioms density_quarter_divisor_moment
end ChenEffective.H10Band
end
