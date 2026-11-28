import GRHQuarterTailAssembly
import GRHH10MediumMass

noncomputable section
namespace ChenEffective.H10Band
open Real Finset
open ChenEffective.GRH (source_multSum_le source_reciprocal_divisor_mass)
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

theorem quarter_conditioned_multSum_eq {N q d : ℕ}
    (hq : q ∈ jurkatRichertSourceMediumPrimes N)
    (hd : d ∣ jurkatRichertSourceSiftingProduct N) :
    (jurkatRichertSourceConditionedBoundingSieve N q).multSum d =
      (jurkatRichertSourceBoundingSieve N).multSum (q*d) := by
  classical
  have hcop := jurkatRichertSourceMediumPrime_coprime_siftingDivisor hq hd
  unfold BoundingSieve.multSum
  change (∑ a ∈ (jurkatRichertSourceUnsiftedComplements N).filter (fun a => q ∣ a),
    if d ∣ a then (1:ℝ) else 0) = _
  rw [sum_filter]
  apply sum_congr rfl
  intro a ha
  change (if q ∣ a then (if d ∣ a then (1:ℝ) else 0) else 0) =
    (if q*d ∣ a then 1 else 0)
  by_cases hqa : q ∣ a
  · by_cases hda : d ∣ a
    · simp [hqa,hda,hcop.mul_dvd_of_dvd_of_dvd hqa hda]
    · have hh : ¬ q*d ∣ a := fun h => hda ((dvd_mul_left d q).trans h)
      simp [hqa,hda,hh]
  · have hh : ¬ q*d ∣ a := fun h => hqa ((dvd_mul_right q d).trans h)
    simp [hqa,hh]

theorem quarter_conditioned_rem_majorant {N q d : ℕ} (hN : 2<N) (hEven : Even N)
    (hq : q ∈ jurkatRichertSourceMediumPrimes N)
    (hd : d ∣ jurkatRichertSourceSiftingProduct N) :
    let S := jurkatRichertSourceConditionedBoundingSieve N q
    |S.rem d| ≤ (N:ℝ)/((q:ℝ)*d)+S.nu d*|S.totalMass| := by
  let S := jurkatRichertSourceConditionedBoundingSieve N q
  have hqp : 0<q := (mem_filter.mp hq).2.1.pos
  have hdp : 0<d := by
    apply Nat.pos_of_ne_zero
    intro hz
    subst d
    exact jurkatRichertSourceSiftingProduct_ne_zero N (zero_dvd_iff.mp hd)
  have hc := source_multSum_le hN hEven (Nat.mul_pos hqp hdp)
  rw [← quarter_conditioned_multSum_eq hq hd,Nat.cast_mul] at hc
  have hc0 : 0≤ S.multSum d := by
    unfold BoundingSieve.multSum
    apply sum_nonneg
    intro a _
    split_ifs <;> norm_num [S,jurkatRichertSourceConditionedBoundingSieve]
  have hnu : 0≤ S.nu d := (S.nu_pos_of_dvd_prodPrimes hd).le
  change |S.multSum d-S.nu d*S.totalMass| ≤ _
  calc
    _ ≤ |S.multSum d|+|S.nu d*S.totalMass| := abs_sub _ _
    _ = S.multSum d+S.nu d*|S.totalMass| := by
      rw [abs_of_nonneg hc0,abs_mul,abs_of_nonneg hnu]
    _ ≤ _ := add_le_add hc le_rfl

theorem conditioned_quarter_rem_moment {N q d : ℕ} (hN : 2<N) (hEven : Even N)
    (hq : q ∈ jurkatRichertSourceMediumPrimes N)
    (hd : d ∣ restrictedSievePrimeProduct (jurkatRichertSourceBoundingSieve N) 4000000) :
    let S := jurkatRichertSourceConditionedBoundingSieve N q
    let Q := smallSievePrimeProduct S 4000000
    (∑ a ∈ Q.divisors, quarterRoot (a:ℝ)*|S.rem (a*d)|) ≤
      ((N:ℝ)/(q:ℝ))/(d:ℝ)*exp (1799/100:ℝ)+|S.totalMass| * S.nu d*exp (1799/100:ℝ) := by
  let S := jurkatRichertSourceConditionedBoundingSieve N q
  let Q := smallSievePrimeProduct S 4000000
  let R := restrictedSievePrimeProduct S 4000000
  have hcop : Q.Coprime R := sieve_prime_partition_coprime S 4000000
  have hpart : Q*R=S.prodPrimes := sieve_prime_partition S 4000000
  have hdR : d ∣ R := hd
  have hdS : d ∣ S.prodPrimes := by rw [← hpart]; exact hdR.trans (dvd_mul_left R Q)
  have hnud : 0≤ S.nu d := (S.nu_pos_of_dvd_prodPrimes hdS).le
  have hmajor : ∀ a ∈ Q.divisors,
      |S.rem (a*d)| ≤ (((N:ℝ)/(q:ℝ))/(d:ℝ))/(a:ℝ)+(|S.totalMass| * S.nu d)*S.nu a := by
    intro a ha
    have haQ := Nat.dvd_of_mem_divisors ha
    have hadS : a*d ∣ S.prodPrimes := by rw [← hpart]; exact Nat.mul_dvd_mul haQ hdR
    have hnu := S.nu_mult.map_mul_of_coprime ((hcop.of_dvd_left haQ).of_dvd_right hdR)
    have hh := quarter_conditioned_rem_majorant hN hEven hq hadS
    change |S.rem (a*d)| ≤ (N:ℝ)/((q:ℝ)*((a*d:ℕ):ℝ))+S.nu (a*d)*|S.totalMass| at hh
    apply hh.trans_eq
    rw [hnu,Nat.cast_mul]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hm := source_quarter_divisor_moments N
  change (∑ a ∈ Q.divisors, 1/quarterRoot (a:ℝ)^3) ≤ exp (1799/100:ℝ) ∧
    (∑ a ∈ Q.divisors, quarterRoot (a:ℝ)*S.nu a) ≤ exp (1799/100:ℝ) at hm
  calc
    _ ≤ ∑ a ∈ Q.divisors, quarterRoot (a:ℝ)*
        ((((N:ℝ)/(q:ℝ))/(d:ℝ))/(a:ℝ)+(|S.totalMass| * S.nu d)*S.nu a) := by
      apply sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (hmajor a ha) (quarterRoot_nonneg _)
    _ = (((N:ℝ)/(q:ℝ))/(d:ℝ))*(∑ a ∈ Q.divisors, 1/quarterRoot (a:ℝ)^3)+
        (|S.totalMass| * S.nu d)*(∑ a ∈ Q.divisors, quarterRoot (a:ℝ)*S.nu a) := by
      rw [mul_sum,mul_sum,← sum_add_distrib]
      apply sum_congr rfl
      intro a _
      calc
        _ = (((N:ℝ)/(q:ℝ))/(d:ℝ))*(quarterRoot (a:ℝ)/(a:ℝ))+
          (|S.totalMass| * S.nu d)*(quarterRoot (a:ℝ)*S.nu a) := by ring
        _ = _ := by rw [quarterRoot_div_self (Nat.cast_nonneg a)]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hm.1 (by positivity))
      (mul_le_mul_of_nonneg_left hm.2 (mul_nonneg (abs_nonneg _) hnud))

theorem conditioned_quarter_tail_aggregate {N q D C : ℕ} (hN : 2<N) (hEven : Even N)
    (hq : q ∈ jurkatRichertSourceMediumPrimes N) (hD : 1≤ D) :
    let S := jurkatRichertSourceConditionedBoundingSieve N q
    let Q := smallSievePrimeProduct S 4000000
    let F := (restrictedSievePrimeProduct S 4000000).divisors.filter (fun d => d<D)
    (∑ d ∈ F, ∑ a ∈ Q.divisors, quarterRoot (a:ℝ)*|S.rem (a*d)|)/quarterRoot (C:ℝ) ≤
      (((N:ℝ)/(q:ℝ))*exp (1799/100:ℝ)+|S.totalMass| * exp (1799/100:ℝ))*(1+log (D:ℝ))^2/quarterRoot (C:ℝ) := by
  let S := jurkatRichertSourceConditionedBoundingSieve N q
  let Q := smallSievePrimeProduct S 4000000
  let F := (restrictedSievePrimeProduct S 4000000).divisors.filter (fun d => d<D)
  have hm := source_reciprocal_divisor_mass N D hD
  apply div_le_div_of_nonneg_right _ (quarterRoot_nonneg _)
  calc
    _ ≤ ∑ d ∈ F, (((N:ℝ)/(q:ℝ))/(d:ℝ)*exp (1799/100:ℝ)+|S.totalMass| * S.nu d*exp (1799/100:ℝ)) := by
      apply sum_le_sum
      intro d hd
      exact conditioned_quarter_rem_moment hN hEven hq (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)
    _ = (((N:ℝ)/(q:ℝ))*exp (1799/100:ℝ))*(∑ d ∈ F, 1/(d:ℝ))+
        (|S.totalMass| * exp (1799/100:ℝ))*(∑ d ∈ F, S.nu d) := by
      rw [mul_sum,mul_sum,← sum_add_distrib]
      apply sum_congr rfl
      intro d _
      ring
    _ ≤ (((N:ℝ)/(q:ℝ))*exp (1799/100:ℝ))*(1+log (D:ℝ))^2+
        (|S.totalMass| * exp (1799/100:ℝ))*(1+log (D:ℝ))^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hm.1 (by positivity))
        (mul_le_mul_of_nonneg_left hm.2 (by positivity))
    _ = _ := by ring

theorem conditioned_mass_cap_of_log {N q : ℕ} (hN : 2<N) (hL : (1:ℝ)≤log (N:ℝ))
    (hq : q ∈ jurkatRichertSourceMediumPrimes N) :
    |(jurkatRichertSourceConditionedBoundingSieve N q).totalMass| ≤ 20*(N:ℝ)/(q:ℝ) := by
  have hqp := (mem_filter.mp hq).2.1.two_le
  have hqR : (2:ℝ)≤ q := by exact_mod_cast hqp
  have hqm : 0<(q:ℝ)-1 := by linarith only [hqR]
  have hq0 : (0:ℝ)<q := by linarith only [hqR]
  have hm := source_mass_cap_of_log hN hL
  change |(jurkatRichertSourceBoundingSieve N).totalMass/((q:ℝ)-1)| ≤ _
  rw [abs_div,abs_of_nonneg hqm.le]
  apply (div_le_div_of_nonneg_right hm hqm.le).trans
  apply (div_le_div_iff₀ hqm hq0).mpr
  nlinarith only [mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hqR)]


def conditionedQuarterTail (N q D C : ℕ) : ℝ :=
  let S := jurkatRichertSourceConditionedBoundingSieve N q
  let Q := ChenEffective.smallSievePrimeProduct S 4000000
  let F := (ChenEffective.restrictedSievePrimeProduct S 4000000).divisors.filter (fun d=>d<D)
  (∑ d∈F,∑ a∈Q.divisors,quarterRoot (a:ℝ)*|S.rem (a*d)|)/quarterRoot (C:ℝ)

theorem conditioned_quarter_tail_absolute {N q D C : ℕ} (hN : 2<N) (hEven : Even N)
    (hL : (1:ℝ)≤log (N:ℝ)) (hq : q∈jurkatRichertSourceMediumPrimes N) (hD : 1≤D) :
    conditionedQuarterTail N q D C≤
      21*((N:ℝ)/(q:ℝ))*exp (1799/100:ℝ)*(1+log (D:ℝ))^2/quarterRoot (C:ℝ) := by
  have hh := conditioned_quarter_tail_aggregate (C:=C) hN hEven hq hD
  have hm := conditioned_mass_cap_of_log hN hL hq
  rw [show 20*(N:ℝ)/(q:ℝ)=20*((N:ℝ)/(q:ℝ)) by ring] at hm
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (quarterRoot_nonneg _)
  have he : ((N:ℝ)/(q:ℝ))*exp (1799/100:ℝ)+
      |(jurkatRichertSourceConditionedBoundingSieve N q).totalMass| *exp (1799/100:ℝ)≤
        21*((N:ℝ)/(q:ℝ))*exp (1799/100:ℝ) := by
    have := mul_le_mul_of_nonneg_right hm (exp_pos (1799/100:ℝ)).le
    linarith only [this]
  exact mul_le_mul_of_nonneg_right he (sq_nonneg _)

/-- Aggregation over the actual medium-prime set, with variable sieve levels. -/
theorem medium_quarter_tail_absolute {N C : ℕ} (hN : 2<N) (hEven : Even N)
    (hL : (2400:ℝ)≤log (N:ℝ)) (D : ℕ→ℕ)
    (hD : ∀ q∈jurkatRichertSourceMediumPrimes N,1≤D q)
    (hDN : ∀ q∈jurkatRichertSourceMediumPrimes N,D q≤N) :
    (∑ q∈jurkatRichertSourceMediumPrimes N,conditionedQuarterTail N q (D q) C)≤
      (2541/100:ℝ)*(N:ℝ)*exp (1799/100:ℝ)*(1+log (N:ℝ))^2/quarterRoot (C:ℝ) := by
  let A := 21*(N:ℝ)*exp (1799/100:ℝ)*(1+log (N:ℝ))^2/quarterRoot (C:ℝ)
  have hA : 0≤A := by
    dsimp [A]
    exact div_nonneg (by positivity) (quarterRoot_nonneg _)
  have hm := medium_aggregate_of_reciprocal_majorant hL hA
    (fun q=>conditionedQuarterTail N q (D q) C) (by
      intro q hq
      have ht := conditioned_quarter_tail_absolute (C:=C) hN hEven
        (by linarith only [hL]) hq (hD q hq)
      have hlog := log_le_log (by exact_mod_cast (show 0<D q by have := hD q hq;omega))
        (show (D q:ℝ)≤N by exact_mod_cast hDN q hq)
      have hnon := log_nonneg (show (1:ℝ)≤D q by exact_mod_cast hD q hq)
      have hsq : (1+log (D q:ℝ))^2≤(1+log (N:ℝ))^2 :=
        pow_le_pow_left₀ (by linarith only [hnon]) (by linarith only [hlog]) 2
      apply ht.trans
      have hh := mul_le_mul_of_nonneg_left hsq
        (show 0≤21*((N:ℝ)/(q:ℝ))*exp (1799/100:ℝ) by positivity)
      have hh' := div_le_div_of_nonneg_right hh (quarterRoot_nonneg (C:ℝ))
      apply hh'.trans_eq
      dsimp only [A]
      ring)
  apply hm.trans_eq
  dsimp only [A]
  ring

theorem quarter_tail_polynomial_cap {L : ℝ} (hL : 2400≤L) :
    (2541/100:ℝ)*(1+L)^2*L^2≤26*L^4 := by
  have hnon : 0≤L := by linarith only [hL]
  have hs : (1+L)^2≤((2401/2400:ℝ)*L)^2 :=
    pow_le_pow_left₀ (by linarith only [hL]) (by linarith only [hL]) 2
  have hh := mul_le_mul_of_nonneg_left hs
    (show 0≤(2541/100:ℝ)*L^2 by positivity)
  nlinarith only [hh,sq_nonneg (L^2)]

/-- Normalized by N/log(N)^2, the currently proved absolute-tail route
has a 26 L^4 prefactor. This theorem does not assert the proposed 16 L. -/
theorem medium_quarter_tail_normalized {N C : ℕ} (hN : 2<N) (hEven : Even N)
    (hL : (2400:ℝ)≤log (N:ℝ)) (D : ℕ→ℕ)
    (hD : ∀ q∈jurkatRichertSourceMediumPrimes N,1≤D q)
    (hDN : ∀ q∈jurkatRichertSourceMediumPrimes N,D q≤N) :
    (∑ q∈jurkatRichertSourceMediumPrimes N,conditionedQuarterTail N q (D q) C)≤
      ((N:ℝ)/log (N:ℝ)^2)*
        (26*log (N:ℝ)^4*exp (1799/100:ℝ)/quarterRoot (C:ℝ)) := by
  have hm := medium_quarter_tail_absolute (C:=C) hN hEven hL D hD hDN
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hp := quarter_tail_polynomial_cap hL
  have hp' : (2541/100:ℝ)*(1+log (N:ℝ))^2≤26*log (N:ℝ)^2 := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hl)).mp
    nlinarith only [hp]
  have hh := mul_le_mul_of_nonneg_left hp'
    (show 0≤(N:ℝ)*exp (1799/100:ℝ) by positivity)
  have hh' := div_le_div_of_nonneg_right hh (quarterRoot_nonneg (C:ℝ))
  apply hm.trans
  convert hh' using 1 <;> field_simp [ne_of_gt hl] <;> ring

#print axioms conditioned_quarter_tail_aggregate
#print axioms medium_quarter_tail_absolute
#print axioms medium_quarter_tail_normalized
end ChenEffective.H10Band
end
