import GRHSourceTail
import GRH14TruncationBudget
import NumericalWeightedMass

noncomputable section
namespace ChenEffective.GRH
open Real Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.LinearSieve
open MathlibNt.SieveTheory.SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem source_root_rem_moment {N d : ℕ} (hN : 2 < N) (hEven : Even N)
    (hd : d ∣ restrictedSievePrimeProduct (jurkatRichertSourceBoundingSieve N) 4000000) :
    let S := jurkatRichertSourceBoundingSieve N
    let Q := smallSievePrimeProduct S 4000000
    (∑ a ∈ Q.divisors, sqrt (a:ℝ)*|S.rem (a*d)|) ≤
      (N:ℝ)/(d:ℝ)*exp 1700+|S.totalMass| * S.nu d*exp 2126 := by
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
  have hm := source_small_prime_divisor_moments N
  change (∑ a ∈ Q.divisors, 1/sqrt (a:ℝ)) ≤ exp 1700 ∧
    (∑ a ∈ Q.divisors, sqrt (a:ℝ)*S.nu a) ≤ exp 2126 at hm
  calc
    _ ≤ ∑ a ∈ Q.divisors, sqrt (a:ℝ)*
        (((N:ℝ)/(d:ℝ))/(a:ℝ)+(|S.totalMass| * S.nu d)*S.nu a) := by
      apply sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (hmajor a ha) (sqrt_nonneg _)
    _ = ((N:ℝ)/(d:ℝ))*(∑ a ∈ Q.divisors, 1/sqrt (a:ℝ))+
        (|S.totalMass| * S.nu d)*(∑ a ∈ Q.divisors, sqrt (a:ℝ)*S.nu a) := by
      rw [mul_sum,mul_sum,← sum_add_distrib]
      apply sum_congr rfl
      intro a _
      have hh := sqrt_div_self' (x:=(a:ℝ))
      calc
        _ = ((N:ℝ)/(d:ℝ))*(sqrt (a:ℝ)/(a:ℝ))+
          (|S.totalMass| * S.nu d)*(sqrt (a:ℝ)*S.nu a) := by ring
        _ = _ := by rw [hh]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hm.1 (by positivity))
      (mul_le_mul_of_nonneg_left hm.2 (mul_nonneg (abs_nonneg _) hnud))

theorem source_reciprocal_divisor_mass (N D : ℕ) (hD : 1 ≤ D) :
    let S := jurkatRichertSourceBoundingSieve N
    let F := (restrictedSievePrimeProduct S 4000000).divisors.filter (fun d => d < D)
    (∑ d ∈ F, 1/(d:ℝ)) ≤ (1+log (D:ℝ))^2 ∧
    (∑ d ∈ F, S.nu d) ≤ (1+log (D:ℝ))^2 := by
  let S := jurkatRichertSourceBoundingSieve N
  let R := restrictedSievePrimeProduct S 4000000
  let F := R.divisors.filter (fun d => d < D)
  have hR : R ∣ S.prodPrimes := by rw [← sieve_prime_partition S 4000000]; exact dvd_mul_left _ _
  have hdS : ∀ d ∈ F, d ∣ S.prodPrimes :=
    fun d hd => (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1).trans hR
  have hsq : ∀ d ∈ F, Squarefree d :=
    fun d hd => S.prodPrimes_squarefree.squarefree_of_dvd (hdS d hd)
  have hF : F ⊆ Icc 1 D := by
    intro d hd
    exact mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (hsq d hd).ne_zero,
      (mem_filter.mp hd).2.le⟩
  have hh := numerical_totient_weight_mass 1 hD F hF hsq
  norm_num only [Nat.cast_one,one_pow,show 2*1=2 by norm_num] at hh
  have hnu : (∑ d ∈ F, S.nu d)=(∑ d ∈ F, 1/(d.totient:ℝ)) := by
    apply sum_congr rfl
    intro d hd
    exact jurkatRichertSource_goldbachNu_eq_inv_totient (hdS d hd)
  constructor
  · apply le_trans _ hh
    apply sum_le_sum
    intro d hd
    have hp : (0:ℝ) < d.totient := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hsq d hd).ne_zero)
    apply one_div_le_one_div_of_le hp
    exact_mod_cast Nat.totient_le d
  · rw [hnu]
    exact hh

theorem source_tail_moment_aggregate {N D C : ℕ} (hN : 2 < N) (hEven : Even N)
    (hD : 1 ≤ D) :
    let S := jurkatRichertSourceBoundingSieve N
    let Q := smallSievePrimeProduct S 4000000
    let F := (restrictedSievePrimeProduct S 4000000).divisors.filter (fun d => d < D)
    (∑ d ∈ F, ∑ a ∈ Q.divisors, sqrt (a:ℝ)*|S.rem (a*d)|)/sqrt (C:ℝ) ≤
      ((N:ℝ)*exp 1700+|S.totalMass| * exp 2126)*(1+log (D:ℝ))^2/sqrt (C:ℝ) := by
  let S := jurkatRichertSourceBoundingSieve N
  let Q := smallSievePrimeProduct S 4000000
  let F := (restrictedSievePrimeProduct S 4000000).divisors.filter (fun d => d < D)
  have hm := source_reciprocal_divisor_mass N D hD
  apply div_le_div_of_nonneg_right _ (sqrt_nonneg _)
  calc
    _ ≤ ∑ d ∈ F, ((N:ℝ)/(d:ℝ)*exp 1700+|S.totalMass| * S.nu d*exp 2126) := by
      apply sum_le_sum
      intro d hd
      exact source_root_rem_moment hN hEven (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)
    _ = ((N:ℝ)*exp 1700)*(∑ d ∈ F, 1/(d:ℝ))+
        (|S.totalMass| * exp 2126)*(∑ d ∈ F, S.nu d) := by
      rw [mul_sum,mul_sum,← sum_add_distrib]
      apply sum_congr rfl
      intro d _
      ring
    _ ≤ ((N:ℝ)*exp 1700)*(1+log (D:ℝ))^2+
        (|S.totalMass| * exp 2126)*(1+log (D:ℝ))^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hm.1 (by positivity))
        (mul_le_mul_of_nonneg_left hm.2 (by positivity))
    _ = _ := by ring

#print axioms source_tail_moment_aggregate
end ChenEffective.GRH
