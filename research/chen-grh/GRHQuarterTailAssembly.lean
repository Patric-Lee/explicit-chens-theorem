import GRHQuarterSourceMoments
import GRHLowerRemainderAggregate

noncomputable section
namespace ChenEffective.H10Band
open Real Finset
open ChenEffective.GRH (source_rem_majorant source_reciprocal_divisor_mass)
open MathlibNt.SieveTheory MathlibNt.SieveTheory.LinearSieve
open MathlibNt.SieveTheory.SwitchingPrinciple
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

theorem source_quarter_rem_moment {N d : ℕ} (hN : 2 < N) (hEven : Even N)
    (hd : d ∣ restrictedSievePrimeProduct (jurkatRichertSourceBoundingSieve N) 4000000) :
    let S := jurkatRichertSourceBoundingSieve N
    let Q := smallSievePrimeProduct S 4000000
    (∑ a ∈ Q.divisors, quarterRoot (a:ℝ)*|S.rem (a*d)|) ≤
      (N:ℝ)/(d:ℝ)*exp (1799/100:ℝ)+|S.totalMass| * S.nu d*exp (1799/100:ℝ) := by
  let S := jurkatRichertSourceBoundingSieve N
  let Q := smallSievePrimeProduct S 4000000
  let R := restrictedSievePrimeProduct S 4000000
  have hcop : Q.Coprime R := sieve_prime_partition_coprime S 4000000
  have hpart : Q*R=S.prodPrimes := sieve_prime_partition S 4000000
  have hdS : d ∣ S.prodPrimes := by
    rw [← hpart]
    exact hd.trans (dvd_mul_left R Q)
  have hnud : 0 ≤ S.nu d := (S.nu_pos_of_dvd_prodPrimes hdS).le
  have hmajor : ∀ a ∈ Q.divisors,
      |S.rem (a*d)| ≤ ((N:ℝ)/(d:ℝ))/(a:ℝ)+(|S.totalMass| * S.nu d)*S.nu a := by
    intro a ha
    have haQ := Nat.dvd_of_mem_divisors ha
    have hadS : a*d ∣ S.prodPrimes := by rw [← hpart]; exact Nat.mul_dvd_mul haQ hd
    have hnu := S.nu_mult.map_mul_of_coprime ((hcop.of_dvd_left haQ).of_dvd_right hd)
    have hh := source_rem_majorant hN hEven hadS
    change |S.rem (a*d)| ≤ (N:ℝ)/((a*d:ℕ):ℝ)+S.nu (a*d)*|S.totalMass| at hh
    apply hh.trans_eq
    rw [hnu,Nat.cast_mul]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hm := source_quarter_divisor_moments N
  change (∑ a ∈ Q.divisors, 1/quarterRoot (a:ℝ)^3) ≤ exp (1799/100:ℝ) ∧
    (∑ a ∈ Q.divisors, quarterRoot (a:ℝ)*S.nu a) ≤ exp (1799/100:ℝ) at hm
  calc
    _ ≤ ∑ a ∈ Q.divisors, quarterRoot (a:ℝ)*
        (((N:ℝ)/(d:ℝ))/(a:ℝ)+(|S.totalMass| * S.nu d)*S.nu a) := by
      apply sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (hmajor a ha) (quarterRoot_nonneg _)
    _ = ((N:ℝ)/(d:ℝ))*(∑ a ∈ Q.divisors, 1/quarterRoot (a:ℝ)^3)+
        (|S.totalMass| * S.nu d)*(∑ a ∈ Q.divisors, quarterRoot (a:ℝ)*S.nu a) := by
      rw [mul_sum,mul_sum,← sum_add_distrib]
      apply sum_congr rfl
      intro a _
      have hh := quarterRoot_div_self (Nat.cast_nonneg a)
      calc
        _ = ((N:ℝ)/(d:ℝ))*(quarterRoot (a:ℝ)/(a:ℝ))+
          (|S.totalMass| * S.nu d)*(quarterRoot (a:ℝ)*S.nu a) := by ring
        _ = _ := by rw [hh]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hm.1 (by positivity))
      (mul_le_mul_of_nonneg_left hm.2 (mul_nonneg (abs_nonneg _) hnud))

theorem source_quarter_tail_aggregate {N D C : ℕ} (hN : 2 < N) (hEven : Even N)
    (hD : 1 ≤ D) :
    let S := jurkatRichertSourceBoundingSieve N
    let Q := smallSievePrimeProduct S 4000000
    let F := (restrictedSievePrimeProduct S 4000000).divisors.filter (fun d => d < D)
    (∑ d ∈ F, ∑ a ∈ Q.divisors, quarterRoot (a:ℝ)*|S.rem (a*d)|)/quarterRoot (C:ℝ) ≤
      ((N:ℝ)*exp (1799/100:ℝ)+|S.totalMass| * exp (1799/100:ℝ))*(1+log (D:ℝ))^2/quarterRoot (C:ℝ) := by
  let S := jurkatRichertSourceBoundingSieve N
  let Q := smallSievePrimeProduct S 4000000
  let F := (restrictedSievePrimeProduct S 4000000).divisors.filter (fun d => d < D)
  have hm := source_reciprocal_divisor_mass N D hD
  apply div_le_div_of_nonneg_right _ (quarterRoot_nonneg _)
  calc
    _ ≤ ∑ d ∈ F, ((N:ℝ)/(d:ℝ)*exp (1799/100:ℝ)+|S.totalMass| * S.nu d*exp (1799/100:ℝ)) := by
      apply sum_le_sum
      intro d hd
      exact source_quarter_rem_moment hN hEven (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)
    _ = ((N:ℝ)*exp (1799/100:ℝ))*(∑ d ∈ F, 1/(d:ℝ))+
        (|S.totalMass| * exp (1799/100:ℝ))*(∑ d ∈ F, S.nu d) := by
      rw [mul_sum,mul_sum,← sum_add_distrib]
      apply sum_congr rfl
      intro d _
      ring
    _ ≤ ((N:ℝ)*exp (1799/100:ℝ))*(1+log (D:ℝ))^2+
        (|S.totalMass| * exp (1799/100:ℝ))*(1+log (D:ℝ))^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hm.1 (by positivity))
        (mul_le_mul_of_nonneg_left hm.2 (by positivity))
    _ = _ := by ring

theorem source_mass_cap_of_log {N : ℕ} (hN : 2<N) (hL : (1:ℝ)≤log (N:ℝ)) :
    |(jurkatRichertSourceBoundingSieve N).totalMass|≤10*(N:ℝ) := by
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hh := LiuWeight.liuLogarithmicIntegral_abs_le (2/log 2)
    (show (2:ℝ)≤N by exact_mod_cast (show 2≤N by omega))
  have hl2 : 0<log (2:ℝ) := log_pos (by norm_num)
  have hk : (2:ℝ)/log 2≤4 := (div_le_iff₀ hl2).mpr (by linarith only [log_two_gt_d9])
  have hk0 : 0≤(2:ℝ)/log 2 := by positivity
  have hc : LiuWeight.liuLogarithmicIntegralUpperConstant (2/log 2)≤10 := by
    unfold LiuWeight.liuLogarithmicIntegralUpperConstant
    rw [abs_of_nonneg hk0]
    linarith only [hk]
  apply hh.trans
  apply (div_le_iff₀ hl).mpr
  have hh := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg N)
  nlinarith only [hh,hL,mul_nonneg (Nat.cast_nonneg N)
    (show 0≤log (N:ℝ)-1 by linarith only [hL])]

/-- Actual absolute tail bound at the finite scale; it retains the divisor-mass factor. -/
theorem source_quarter_tail_absolute {N D C : ℕ} (hN : 2<N) (hEven : Even N)
    (hL : (1:ℝ)≤log (N:ℝ)) (hD : 1≤D) :
    let S := jurkatRichertSourceBoundingSieve N
    let Q := smallSievePrimeProduct S 4000000
    let F := (restrictedSievePrimeProduct S 4000000).divisors.filter (fun d=>d<D)
    (∑ d∈F,∑ a∈Q.divisors,quarterRoot (a:ℝ)*|S.rem (a*d)|)/quarterRoot (C:ℝ)≤
      11*(N:ℝ)*exp (1799/100:ℝ)*(1+log (D:ℝ))^2/quarterRoot (C:ℝ) := by
  have hh := source_quarter_tail_aggregate (C:=C) hN hEven hD
  have hm := source_mass_cap_of_log hN hL
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (quarterRoot_nonneg _)
  have he : ((N:ℝ)*exp (1799/100:ℝ)+
      |(jurkatRichertSourceBoundingSieve N).totalMass| *exp (1799/100:ℝ))≤
        11*(N:ℝ)*exp (1799/100:ℝ) := by
    have := mul_le_mul_of_nonneg_right hm (exp_pos (1799/100:ℝ)).le
    linarith only [this]
  exact mul_le_mul_of_nonneg_right he (sq_nonneg _)

/-- The improved finite moment is attached to the actual pre-sieved remainder.
The distribution sum at range C*D is retained as an explicit obligation. -/
theorem source_errSum_quarter {N D C : ℕ} (hN : 2<N) (hEven : Even N)
    (hL : (1:ℝ)≤log (N:ℝ)) (hD : 1≤D) (hC : 0<C) (weight : ℕ→ℝ)
    (hsupp : ∀ d,d∣restrictedSievePrimeProduct (jurkatRichertSourceBoundingSieve N) 4000000 →
      ¬d<D → weight d=0)
    (hweight : ∀ d,d∣restrictedSievePrimeProduct (jurkatRichertSourceBoundingSieve N) 4000000 →
      |weight d|≤1) :
    let S := jurkatRichertSourceBoundingSieve N
    (preSieveCounting S 4000000).errSum weight≤ sieveRemainderBelow S (C*D)+
      11*(N:ℝ)*exp (1799/100:ℝ)*(1+log (D:ℝ))^2/quarterRoot (C:ℝ) := by
  have hh := preSieve_errSum_truncated_sigma (jurkatRichertSourceBoundingSieve N)
    4000000 D C hC (1/4:ℝ) (by norm_num) weight hsupp hweight
  have he (n : ℕ) : (n:ℝ)^(1/4:ℝ)=quarterRoot (n:ℝ) :=
    (quarterRoot_rpow (Nat.cast_nonneg n)).symm
  simp only [he] at hh
  have ht := source_quarter_tail_absolute (C:=C) hN hEven hL hD
  linarith only [hh,ht]

#print axioms source_quarter_rem_moment
#print axioms source_quarter_tail_aggregate
#print axioms source_quarter_tail_absolute
#print axioms source_errSum_quarter
end ChenEffective.H10Band
end
