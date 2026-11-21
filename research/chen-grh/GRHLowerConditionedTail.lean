import GRH14LowerTailPayment

noncomputable section
namespace ChenEffective.GRH
open Real Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem conditioned_multSum_eq {N q d : ℕ}
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

theorem conditioned_rem_majorant {N q d : ℕ} (hN : 2<N) (hEven : Even N)
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
  rw [← conditioned_multSum_eq hq hd,Nat.cast_mul] at hc
  have hc0 : 0≤S.multSum d := by
    unfold BoundingSieve.multSum
    apply sum_nonneg
    intro a _
    split_ifs <;> norm_num [S,jurkatRichertSourceConditionedBoundingSieve]
  have hnu : 0≤S.nu d := (S.nu_pos_of_dvd_prodPrimes hd).le
  change |S.multSum d-S.nu d*S.totalMass| ≤ _
  calc
    _ ≤ |S.multSum d|+|S.nu d*S.totalMass| := abs_sub _ _
    _ = S.multSum d+S.nu d*|S.totalMass| := by
      rw [abs_of_nonneg hc0,abs_mul,abs_of_nonneg hnu]
    _ ≤ _ := add_le_add hc le_rfl

theorem conditioned_root_rem_moment {N q d : ℕ} (hN : 2<N) (hEven : Even N)
    (hq : q ∈ jurkatRichertSourceMediumPrimes N)
    (hd : d ∣ restrictedSievePrimeProduct (jurkatRichertSourceBoundingSieve N) 4000000) :
    let S := jurkatRichertSourceConditionedBoundingSieve N q
    let Q := smallSievePrimeProduct S 4000000
    (∑ a ∈ Q.divisors, sqrt (a:ℝ)*|S.rem (a*d)|) ≤
      ((N:ℝ)/(q:ℝ))/(d:ℝ)*exp 1700+|S.totalMass| * S.nu d*exp 2126 := by
  let S := jurkatRichertSourceConditionedBoundingSieve N q
  let Q := smallSievePrimeProduct S 4000000
  let R := restrictedSievePrimeProduct S 4000000
  have hcop : Q.Coprime R := sieve_prime_partition_coprime S 4000000
  have hpart : Q*R=S.prodPrimes := sieve_prime_partition S 4000000
  have hdR : d ∣ R := hd
  have hdS : d ∣ S.prodPrimes := by rw [← hpart]; exact hdR.trans (dvd_mul_left R Q)
  have hnud : 0≤S.nu d := (S.nu_pos_of_dvd_prodPrimes hdS).le
  have hmajor : ∀ a ∈ Q.divisors,
      |S.rem (a*d)| ≤ (((N:ℝ)/(q:ℝ))/(d:ℝ))/(a:ℝ)+(|S.totalMass| * S.nu d)*S.nu a := by
    intro a ha
    have haQ := Nat.dvd_of_mem_divisors ha
    have hadS : a*d ∣ S.prodPrimes := by rw [← hpart]; exact Nat.mul_dvd_mul haQ hdR
    have hnu := S.nu_mult.map_mul_of_coprime ((hcop.of_dvd_left haQ).of_dvd_right hdR)
    have hh := conditioned_rem_majorant hN hEven hq hadS
    change |S.rem (a*d)| ≤ (N:ℝ)/((q:ℝ)*((a*d:ℕ):ℝ))+S.nu (a*d)*|S.totalMass| at hh
    apply hh.trans_eq
    rw [hnu,Nat.cast_mul]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hm := source_small_prime_divisor_moments N
  change (∑ a ∈ Q.divisors, 1/sqrt (a:ℝ)) ≤ exp 1700 ∧
    (∑ a ∈ Q.divisors, sqrt (a:ℝ)*S.nu a) ≤ exp 2126 at hm
  calc
    _ ≤ ∑ a ∈ Q.divisors, sqrt (a:ℝ)*
        ((((N:ℝ)/(q:ℝ))/(d:ℝ))/(a:ℝ)+(|S.totalMass| * S.nu d)*S.nu a) := by
      apply sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (hmajor a ha) (sqrt_nonneg _)
    _ = (((N:ℝ)/(q:ℝ))/(d:ℝ))*(∑ a ∈ Q.divisors, 1/sqrt (a:ℝ))+
        (|S.totalMass| * S.nu d)*(∑ a ∈ Q.divisors, sqrt (a:ℝ)*S.nu a) := by
      rw [mul_sum,mul_sum,← sum_add_distrib]
      apply sum_congr rfl
      intro a _
      calc
        _ = (((N:ℝ)/(q:ℝ))/(d:ℝ))*(sqrt (a:ℝ)/(a:ℝ))+
          (|S.totalMass| * S.nu d)*(sqrt (a:ℝ)*S.nu a) := by ring
        _ = _ := by rw [sqrt_div_self']
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hm.1 (by positivity))
      (mul_le_mul_of_nonneg_left hm.2 (mul_nonneg (abs_nonneg _) hnud))

theorem conditioned_tail_moment_aggregate {N q D C : ℕ} (hN : 2<N) (hEven : Even N)
    (hq : q ∈ jurkatRichertSourceMediumPrimes N) (hD : 1≤D) :
    let S := jurkatRichertSourceConditionedBoundingSieve N q
    let Q := smallSievePrimeProduct S 4000000
    let F := (restrictedSievePrimeProduct S 4000000).divisors.filter (fun d => d<D)
    (∑ d ∈ F, ∑ a ∈ Q.divisors, sqrt (a:ℝ)*|S.rem (a*d)|)/sqrt (C:ℝ) ≤
      (((N:ℝ)/(q:ℝ))*exp 1700+|S.totalMass| * exp 2126)*(1+log (D:ℝ))^2/sqrt (C:ℝ) := by
  let S := jurkatRichertSourceConditionedBoundingSieve N q
  let Q := smallSievePrimeProduct S 4000000
  let F := (restrictedSievePrimeProduct S 4000000).divisors.filter (fun d => d<D)
  have hm := source_reciprocal_divisor_mass N D hD
  apply div_le_div_of_nonneg_right _ (sqrt_nonneg _)
  calc
    _ ≤ ∑ d ∈ F, (((N:ℝ)/(q:ℝ))/(d:ℝ)*exp 1700+|S.totalMass| * S.nu d*exp 2126) := by
      apply sum_le_sum
      intro d hd
      exact conditioned_root_rem_moment hN hEven hq (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)
    _ = (((N:ℝ)/(q:ℝ))*exp 1700)*(∑ d ∈ F, 1/(d:ℝ))+
        (|S.totalMass| * exp 2126)*(∑ d ∈ F, S.nu d) := by
      rw [mul_sum,mul_sum,← sum_add_distrib]
      apply sum_congr rfl
      intro d _
      ring
    _ ≤ (((N:ℝ)/(q:ℝ))*exp 1700)*(1+log (D:ℝ))^2+
        (|S.totalMass| * exp 2126)*(1+log (D:ℝ))^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hm.1 (by positivity))
        (mul_le_mul_of_nonneg_left hm.2 (by positivity))
    _ = _ := by ring

#print axioms conditioned_tail_moment_aggregate
end ChenEffective.GRH
