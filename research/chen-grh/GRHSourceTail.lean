import GRHTruncatedPreSieve
import GRHDivisorMoments

/-! Counting positive multiples has no additive endpoint loss. This is the
point needed to avoid a factor equal to the number of pre-sieve divisors. -/
noncomputable section
namespace ChenEffective.GRH
open Real Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.LinearSieve
set_option maxHeartbeats 3000000

theorem positive_multiples_card (F : Finset ℕ) (N d : ℕ) (hd : 0 < d)
    (hF : ∀ a ∈ F, 0 < a ∧ a ≤ N) :
    (F.filter (fun a => d ∣ a)).card ≤ N/d := by
  classical
  let T := F.filter (fun a => d ∣ a)
  have hinj : Set.InjOn (fun a : ℕ => a/d) (↑T : Set ℕ) := by
    intro a ha b hb hab
    have hda := (mem_filter.mp ha).2
    have hdb := (mem_filter.mp hb).2
    have hma := Nat.div_mul_cancel hda
    have hmb := Nat.div_mul_cancel hdb
    change a/d=b/d at hab
    rw [hab] at hma
    exact hma.symm.trans hmb
  have hsub : T.image (fun a => a/d) ⊆ Icc 1 (N/d) := by
    intro b hb
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hb
    have haF := hF a (mem_filter.mp ha).1
    have hda := (mem_filter.mp ha).2
    apply mem_Icc.mpr
    exact ⟨Nat.div_pos (Nat.le_of_dvd haF.1 hda) hd,
      Nat.div_le_div_right haF.2⟩
  calc
    _ = (T.image (fun a => a/d)).card := (card_image_of_injOn hinj).symm
    _ ≤ (Icc 1 (N/d)).card := card_le_card hsub
    _ = N/d := by simp

theorem constant_weight_multSum_le (S : BoundingSieve) {N d : ℕ}
    (hd : 0 < d) (hsupport : ∀ a ∈ S.support, 0 < a ∧ a ≤ N)
    (hweights : ∀ a ∈ S.support, S.weights a=1) :
    S.multSum d ≤ (N:ℝ)/(d:ℝ) := by
  have hc := positive_multiples_card S.support N d hd hsupport
  have heq : S.multSum d = ((S.support.filter (fun a => d ∣ a)).card:ℝ) := by
    unfold BoundingSieve.multSum
    rw [← sum_filter]
    calc
      _ = ∑ a ∈ S.support.filter (fun a => d ∣ a), (1:ℝ) := by
        apply sum_congr rfl
        intro a ha
        exact hweights a (mem_filter.mp ha).1
      _ = _ := by simp
  rw [heq]
  calc
    _ ≤ ((N/d:ℕ):ℝ) := by exact_mod_cast hc
    _ ≤ _ := Nat.cast_div_le

theorem source_support_positive {N : ℕ} (hN : 2 < N) (hEven : Even N) :
    ∀ a ∈ jurkatRichertSourceUnsiftedComplements N, 0 < a ∧ a ≤ N := by
  classical
  have hnprime : ¬ N.Prime := by
    intro hp
    rcases hp.eq_two_or_odd with hh|hh
    · omega
    · obtain ⟨k,hk⟩ := hEven
      omega
  intro a ha
  obtain ⟨p,hp,rfl⟩ := mem_image.mp ha
  have hpp := (mem_filter.mp hp).2.1
  have hpN := mem_range.mp (mem_filter.mp hp).1
  have hne : p ≠ N := by intro hh; subst p; exact hnprime hpp
  exact ⟨Nat.sub_pos_of_lt (by omega),Nat.sub_le _ _⟩

theorem source_multSum_le {N d : ℕ} (hN : 2 < N) (hEven : Even N) (hd : 0 < d) :
    (jurkatRichertSourceBoundingSieve N).multSum d ≤ (N:ℝ)/(d:ℝ) := by
  exact constant_weight_multSum_le (jurkatRichertSourceBoundingSieve N) hd
    (source_support_positive hN hEven) (fun _ _ => rfl)

/-- A reciprocal majorant for the exact source discrepancy. In particular,
there is no additive `1` for each pre-sieve divisor. -/
theorem source_rem_majorant {N d : ℕ} (hN : 2 < N) (hEven : Even N)
    (hd : d ∣ jurkatRichertSourceSiftingProduct N) :
    |(jurkatRichertSourceBoundingSieve N).rem d| ≤
      (N:ℝ)/(d:ℝ)+AnalyticNumberTheory.Sieve.goldbachNu d*
        |(jurkatRichertSourceBoundingSieve N).totalMass| := by
  let S := jurkatRichertSourceBoundingSieve N
  have hd0 : 0 < d := by
    by_contra hh
    have hz : d=0 := by omega
    subst d
    exact jurkatRichertSourceSiftingProduct_ne_zero N (zero_dvd_iff.mp hd)
  have hcount := source_multSum_le hN hEven hd0
  have hcount0 : 0 ≤ S.multSum d := by
    unfold BoundingSieve.multSum
    apply sum_nonneg
    intro a ha
    split_ifs
    · exact S.weights_nonneg a
    · exact le_refl 0
  have hnu : 0 ≤ S.nu d := (S.nu_pos_of_dvd_prodPrimes hd).le
  change |S.multSum d-S.nu d*S.totalMass| ≤ _
  calc
    _ ≤ |S.multSum d|+|S.nu d*S.totalMass| := abs_sub _ _
    _ = S.multSum d+S.nu d*|S.totalMass| := by
      rw [abs_of_nonneg hcount0,abs_mul,abs_of_nonneg hnu]
    _ ≤ _ := add_le_add hcount le_rfl

theorem source_presieve_rem_truncated {N d C : ℕ} (hN : 2 < N)
    (hEven : Even N) (hC : 0 < C)
    (hd : d ∣ restrictedSievePrimeProduct (jurkatRichertSourceBoundingSieve N) 4000000) :
    let S := jurkatRichertSourceBoundingSieve N
    let Q := smallSievePrimeProduct S 4000000
    |(preSieveCounting S 4000000).rem d| ≤
      (∑ a ∈ Q.divisors.filter (fun a => a ≤ C), |S.rem (a*d)|) +
      ((N:ℝ)/(d:ℝ)*exp 1700+|S.totalMass| * S.nu d*exp 2126)/sqrt (C:ℝ) := by
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
    have hadS : a*d ∣ S.prodPrimes := by
      rw [← hpart]
      exact Nat.mul_dvd_mul haQ hd
    have hnu := S.nu_mult.map_mul_of_coprime ((hcop.of_dvd_left haQ).of_dvd_right hd)
    have hh := source_rem_majorant hN hEven hadS
    change |S.rem (a*d)| ≤ (N:ℝ)/((a*d:ℕ):ℝ)+S.nu (a*d)*|S.totalMass| at hh
    apply hh.trans_eq
    rw [hnu,Nat.cast_mul]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hbound := preSieve_rem_truncated_moments S 4000000 hd hC
    ((N:ℝ)/(d:ℝ)) (|S.totalMass| * S.nu d) S.nu hmajor
  have hm := source_small_prime_divisor_moments N
  change (∑ a ∈ Q.divisors, 1/sqrt (a:ℝ)) ≤ exp 1700 ∧
    (∑ a ∈ Q.divisors, sqrt (a:ℝ)*S.nu a) ≤ exp 2126 at hm
  apply hbound.trans
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ (sqrt_nonneg _)
  simp_rw [sqrt_div_self']
  exact add_le_add (mul_le_mul_of_nonneg_left hm.1 (by positivity))
    (mul_le_mul_of_nonneg_left hm.2 (mul_nonneg (abs_nonneg _) hnud))

#print axioms source_presieve_rem_truncated
#print axioms source_rem_majorant
#print axioms source_multSum_le
#print axioms constant_weight_multSum_le
end ChenEffective.GRH
