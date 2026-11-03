import NumericalBV
import MathlibNt.SieveTheory.LinearSieve.Richert.Richert1969Ordinary418Specialization

/-! Finite totient-weighted Cauchy payment. Uses the already-imported elementary
ordered-divisor helper, without Mertens witnesses or additional dependencies. -/
namespace ChenEffective
open Finset
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.Richert1969
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem ordered_divisor_squarefree (k n : ℕ) (hn : Squarefree n) :
    fouvryTau k n = k ^ n.primeFactors.card := by
  rw [← (fouvryTau_multiplicative k).prod_primeFactors hn]
  have hp (p : ℕ) (hpm : p ∈ n.primeFactors) : fouvryTau k p = k := by
    have hh := fouvryTau_prime_pow (Nat.prime_of_mem_primeFactors hpm) k 1
    simpa [Nat.multichoose_eq] using hh
  simp_rw [Finset.prod_congr rfl hp]
  simp

theorem numerical_totient_weight_mass (k : ℕ) {Q : ℕ} (hQ : 1 ≤ Q) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 Q) (hsq : ∀ d ∈ S, Squarefree d) :
    (∑ d ∈ S, (k : ℝ) ^ d.primeFactors.card / d.totient) ≤
      (1 + Real.log (Q : ℝ)) ^ (2 * k) := by
  have hh := sum_fouvryTau_div_totient_le_real k
    (show (1 : ℝ) ≤ Q by exact_mod_cast hQ)
  simp only [Nat.floor_natCast] at hh
  apply le_trans _ hh
  have heq : (∑ d ∈ S, (k : ℝ) ^ d.primeFactors.card / d.totient) =
      ∑ d ∈ S, (fouvryTau k d : ℝ) / d.totient := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [ordered_divisor_squarefree k d (hsq d hd), Nat.cast_pow]
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    have hm := Finset.mem_Icc.mp (hS hd)
    exact Finset.mem_Ioc.mpr ⟨hm.1, hm.2⟩
  · intro d _ _
    positivity

theorem numerical_totient_nine_mass {Q : ℕ} (hQ : 1 ≤ Q) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 Q) (hsq : ∀ d ∈ S, Squarefree d) :
    (∑ d ∈ S, (9 : ℝ) ^ d.primeFactors.card / d.totient) ≤
      (1 + Real.log (Q : ℝ)) ^ (18 : ℕ) :=
  numerical_totient_weight_mass 9 hQ S hS hsq

theorem numerical_totient_cauchy (S : Finset ℕ) (w E : ℕ → ℝ) (X : ℝ)
    (hd : ∀ d ∈ S, 0 < d) (hE : ∀ d ∈ S, 0 ≤ E d)
    (henvelope : ∀ d ∈ S, (d.totient : ℝ) * E d ≤ X) :
    (∑ d ∈ S, w d * E d) ^ 2 ≤
      (∑ d ∈ S, w d ^ 2 / (d.totient : ℝ)) * (X * ∑ d ∈ S, E d) := by
  let a : ℕ → ℝ := fun d => w d / Real.sqrt d.totient
  let b : ℕ → ℝ := fun d => Real.sqrt d.totient * E d
  have hab : (∑ d ∈ S, w d * E d) = ∑ d ∈ S, a d * b d := by
    apply Finset.sum_congr rfl
    intro d hdS
    have hp : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr (hd d hdS)
    have hsqrt : Real.sqrt (d.totient : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hp
    dsimp [a, b]
    field_simp
  rw [hab]
  refine (Finset.sum_mul_sq_le_sq_mul_sq S a b).trans ?_
  have ha : (∑ d ∈ S, a d ^ 2) = ∑ d ∈ S, w d ^ 2 / (d.totient : ℝ) := by
    apply Finset.sum_congr rfl
    intro d _
    dsimp [a]
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hb : (∑ d ∈ S, b d ^ 2) ≤ X * ∑ d ∈ S, E d := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hdS
    calc
      b d ^ 2 = (d.totient : ℝ) * E d ^ 2 := by
        dsimp [b]
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      _ = ((d.totient : ℝ) * E d) * E d := by ring
      _ ≤ X * E d := mul_le_mul_of_nonneg_right (henvelope d hdS) (hE d hdS)
  rw [ha]
  exact mul_le_mul_of_nonneg_left hb (Finset.sum_nonneg fun _ _ => by positivity)

#print axioms numerical_totient_nine_mass
#print axioms numerical_totient_cauchy
end ChenEffective
