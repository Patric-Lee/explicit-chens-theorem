import GRHTruncatedPreSieve
import GRHDivisorMoments

/-! Truncation of the exact pre-sieve expansion.  The tail is controlled by
variable-exponent weighted moments rather than the entire prime product.
All estimates in this file are elementary; no GRH hypothesis is used. -/
noncomputable section
namespace ChenEffective.H10Band
open ChenEffective.GRH
open Real Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.LinearSieve
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem tail_rankin_sigma (F : Finset ℕ) (C : ℕ) (hC : 0 < C) (σ : ℝ) (hσ : 0≤σ)
    (f : ℕ → ℝ) (hf : ∀ a ∈ F, 0 ≤ f a) :
    (∑ a ∈ F.filter (fun a => C < a), f a) ≤
      (∑ a ∈ F, ((a:ℝ)^σ)*f a)/((C:ℝ)^σ) := by
  have hCp : (0:ℝ) < C := by exact_mod_cast hC
  apply (le_div_iff₀ (rpow_pos_of_pos hCp σ)).mpr
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ a ∈ F.filter (fun a => C < a), ((a:ℝ)^σ)*f a := by
      apply sum_le_sum
      intro a ha
      have hca : (C:ℝ) ≤ a := by
        exact_mod_cast (Nat.le_of_lt (mem_filter.mp ha).2)
      nlinarith only [mul_le_mul_of_nonneg_right (rpow_le_rpow (Nat.cast_nonneg C) hca hσ)
        (hf a (mem_filter.mp ha).1)]
    _ ≤ ∑ a ∈ F, ((a:ℝ)^σ)*f a :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun a ha _ => mul_nonneg (rpow_nonneg (Nat.cast_nonneg _) σ) (hf a ha))

theorem preSieve_rem_truncated_sigma (S : BoundingSieve) (U : ℝ) {d C : ℕ}
    (hd : d ∣ restrictedSievePrimeProduct S U) (hC : 0 < C) (σ : ℝ) (hσ : 0≤σ) :
    |(preSieveCounting S U).rem d| ≤
      (∑ a ∈ (smallSievePrimeProduct S U).divisors.filter (fun a => a ≤ C),
        |S.rem (a*d)|) +
      (∑ a ∈ (smallSievePrimeProduct S U).divisors,
        ((a:ℝ)^σ)*|S.rem (a*d)|)/((C:ℝ)^σ) := by
  have hsplit := sum_filter_add_sum_filter_not
    (smallSievePrimeProduct S U).divisors (fun a => a ≤ C)
    (fun a => |S.rem (a*d)|)
  have htail := tail_rankin_sigma (smallSievePrimeProduct S U).divisors C hC σ hσ
    (fun a => |S.rem (a*d)|) (fun _ _ => abs_nonneg _)
  simp only [not_le] at hsplit
  exact (preSieveCounting_rem_abs S U hd).trans (by linarith only [hsplit,htail])

/-- A useful form for the application: only small divisors use AP
distribution. Large divisors are paid for using reciprocal and density
moments. The pointwise majorant is an explicit premise, not an axiom. -/
theorem preSieve_rem_truncated_moments_sigma (S : BoundingSieve) (U : ℝ) {d C : ℕ}
    (hd : d ∣ restrictedSievePrimeProduct S U) (hC : 0 < C) (σ : ℝ) (hσ : 0≤σ)
    (A B : ℝ) (v : ℕ → ℝ)
    (hrem : ∀ a ∈ (smallSievePrimeProduct S U).divisors,
      |S.rem (a*d)| ≤ A/(a:ℝ)+B*v a) :
    |(preSieveCounting S U).rem d| ≤
      (∑ a ∈ (smallSievePrimeProduct S U).divisors.filter (fun a => a ≤ C),
        |S.rem (a*d)|) +
      (A*(∑ a ∈ (smallSievePrimeProduct S U).divisors, ((a:ℝ)^σ)/(a:ℝ)) +
       B*(∑ a ∈ (smallSievePrimeProduct S U).divisors, ((a:ℝ)^σ)*v a))/
        ((C:ℝ)^σ) := by
  apply (preSieve_rem_truncated_sigma S U hd hC σ hσ).trans
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ (rpow_nonneg (Nat.cast_nonneg _) σ)
  calc
    _ ≤ ∑ a ∈ (smallSievePrimeProduct S U).divisors,
        ((a:ℝ)^σ)*(A/(a:ℝ)+B*v a) := by
      apply sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (hrem a ha) (rpow_nonneg (Nat.cast_nonneg _) σ)
    _ = _ := by
      rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
      apply sum_congr rfl
      intro a ha
      ring

/-- Full finite error assembly with a truncated distribution range `C*D`.
The discarded divisors are retained explicitly as a weighted moment. -/
theorem preSieve_errSum_truncated_sigma (S : BoundingSieve) (U : ℝ) (D C : ℕ)
    (hC : 0 < C) (σ : ℝ) (hσ : 0≤σ) (weight : ℕ → ℝ)
    (hsupp : ∀ d, d ∣ restrictedSievePrimeProduct S U → ¬d < D → weight d = 0)
    (hweight : ∀ d, d ∣ restrictedSievePrimeProduct S U → |weight d| ≤ 1) :
    (preSieveCounting S U).errSum weight ≤ sieveRemainderBelow S (C*D) +
      (∑ d ∈ (restrictedSievePrimeProduct S U).divisors.filter (fun d => d < D),
        ∑ a ∈ (smallSievePrimeProduct S U).divisors,
          ((a:ℝ)^σ)*|S.rem (a*d)|)/((C:ℝ)^σ) := by
  let Q := smallSievePrimeProduct S U
  let R := restrictedSievePrimeProduct S U
  let A := Q.divisors.filter (fun a => a ≤ C)
  let B := R.divisors.filter (fun d => d < D)
  let T := A ×ˢ B
  have hcop : Q.Coprime R := sieve_prime_partition_coprime S U
  have hfull : T ⊆ Q.divisors ×ˢ R.divisors := by
    intro x hx
    exact mem_product.mpr ⟨(mem_filter.mp (mem_product.mp hx).1).1,
      (mem_filter.mp (mem_product.mp hx).2).1⟩
  have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1*x.2) (↑T : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    exact hcop.mul_injOn_divisors (hfull hx) (hfull hy) hxy
  have hsub : T.image (fun x => x.1*x.2) ⊆
      S.prodPrimes.divisors.filter (fun k => k < C*D) := by
    intro k hk
    obtain ⟨⟨a,d⟩,hp,rfl⟩ := mem_image.mp hk
    have ha := mem_filter.mp (mem_product.mp hp).1
    have hd := mem_filter.mp (mem_product.mp hp).2
    apply mem_filter.mpr
    constructor
    · apply Nat.mem_divisors.mpr
      refine ⟨?_,S.prodPrimes_ne_zero⟩
      have hh := Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors ha.1)
        (Nat.dvd_of_mem_divisors hd.1)
      simpa only [Q,R,sieve_prime_partition] using hh
    · exact (Nat.mul_le_mul_right d ha.2).trans_lt
        (Nat.mul_lt_mul_of_pos_left hd.2 hC)
  have hlow : (∑ d ∈ B, ∑ a ∈ A, |S.rem (a*d)|) ≤
      sieveRemainderBelow S (C*D) := by
    calc
      _ = ∑ x ∈ T, |S.rem (x.1*x.2)| := by rw [sum_comm,sum_product]
      _ = ∑ k ∈ T.image (fun x => x.1*x.2), |S.rem k| :=
        (sum_image (f := fun k => |S.rem k|) hinj).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
  unfold BoundingSieve.errSum
  change (∑ d ∈ R.divisors, |weight d| * |(preSieveCounting S U).rem d|) ≤ _
  calc
    _ = ∑ d ∈ B, |weight d| * |(preSieveCounting S U).rem d| := by
      rw [sum_filter]
      apply sum_congr rfl
      intro d hd
      by_cases hdD : d < D
      · simp only [if_pos hdD]
      · simp only [if_neg hdD,hsupp d (Nat.dvd_of_mem_divisors hd) hdD,abs_zero,zero_mul]
    _ ≤ ∑ d ∈ B, ((∑ a ∈ A, |S.rem (a*d)|) +
        (∑ a ∈ Q.divisors, ((a:ℝ)^σ)*|S.rem (a*d)|)/((C:ℝ)^σ)) := by
      apply sum_le_sum
      intro d hd
      have hdR := Nat.dvd_of_mem_divisors (mem_filter.mp hd).1
      exact (le_trans (mul_le_mul_of_nonneg_right (hweight d hdR) (abs_nonneg _))
        (by rw [one_mul])).trans (preSieve_rem_truncated_sigma S U hdR hC σ hσ)
    _ = (∑ d ∈ B, ∑ a ∈ A, |S.rem (a*d)|) +
        (∑ d ∈ B, ∑ a ∈ Q.divisors, ((a:ℝ)^σ)*|S.rem (a*d)|)/((C:ℝ)^σ) := by
      rw [sum_add_distrib,sum_div]
    _ ≤ _ := add_le_add hlow le_rfl

#print axioms preSieve_errSum_truncated_sigma
#print axioms preSieve_rem_truncated_moments_sigma
open ArithmeticFunction

/-- Exact finite Euler product: no replacement log(1+u) <= u is made. -/
theorem squarefree_divisor_moment_exact_log {Q : ℕ} (hQ : Squarefree Q)
    (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative)
    (hpos : ∀ p∈Q.primeFactors,0≤f p) :
    (∑ d∈Q.divisors,f d)=exp (∑ p∈Q.primeFactors,log (1+f p)) := by
  rw [←hf.prodPrimeFactors_one_add_of_squarefree hQ,exp_sum]
  apply prod_congr rfl
  intro p hp
  exact (exp_log (by linarith only [hpos p hp] : (0:ℝ)<1+f p)).symm

#print axioms squarefree_divisor_moment_exact_log
end ChenEffective.H10Band
end
