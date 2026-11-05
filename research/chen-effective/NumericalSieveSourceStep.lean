import NumericalSieveSourceDomination

namespace ChenEffective
open Real Set Finset MeasureTheory intervalIntegral
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- Finite source-native successor assembly. The induction input is only on
the literal recursive natural levels; no surrogate discrete layers occur. -/
theorem actual_source_successor_atom_bound
    {S : BoundingSieve} {n D z : ℕ} {x w v : ℝ} {H : ℝ → ℝ}
    (hn : 0 < n) (hx : 0 < x) (hz : z = ⌈x⌉₊) (hvx : v ≤ x)
    (hcarrier : ∀ p ∈ suzukiSourceOuterCarrierPowerReal (n + 1) D x S.prodPrimes.primeFactors,
      w ≤ (p : ℝ) ∧ (p : ℝ) < v)
    (hinner : ∀ p ∈ suzukiSourceOuterCarrierPowerReal (n + 1) D x S.prodPrimes.primeFactors,
      suzukiSourceV S n (D ⌈/⌉ p) p ≤
        sourceDiscreteEuler S p * H (log (D : ℝ) / log p))
    (hH0 : ∀ p ∈ S.prodPrimes.primeFactors.filter
      (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < v), 0 ≤ H (log (D : ℝ) / log p)) :
    suzukiSourceV S (n + 1) D z ≤
      suzukiVProduct S x * suzukiLemmaEightSevenPrimeSum S (D : ℝ) w v x H := by
  let C := suzukiSourceOuterCarrierPowerReal (n + 1) D x S.prodPrimes.primeFactors
  let P := S.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < v)
  let R := fun p : ℕ => ∏ q ∈ S.prodPrimes.primeFactors.filter
    (fun q : ℕ => p ≤ q ∧ (q : ℝ) < x), (1 - S.nu q)⁻¹
  have hsub : C ⊆ P := by
    intro p hp
    exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hp).1).1, hcarrier p hp⟩
  have hnu : ∀ p ∈ P, 0 ≤ S.nu p := by
    intro p hp
    have hP := (mem_filter.mp hp).1
    exact (S.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hP)
      (Nat.dvd_of_mem_primeFactors hP)).le
  have hR : ∀ p, R p = suzukiLocalRatio S (p : ℝ) x := by
    intro p
    unfold R suzukiLocalRatio
    congr 2
    ext q
    simp
  have hR0 : ∀ p, 0 ≤ R p := by
    intro p
    apply prod_nonneg
    intro q hq
    have hP := (mem_filter.mp hq).1
    exact inv_nonneg.mpr (sub_nonneg.mpr (S.nu_lt_one_of_prime q
      (Nat.prime_of_mem_primeFactors hP) (Nat.dvd_of_mem_primeFactors hP)).le)
  have hV : 0 ≤ suzukiVProduct S x := (suzukiVProduct_pos S x).le
  rw [suzukiSourceV_succ_natCeil_eq_powerReal S hn hx hz]
  calc
    _ ≤ ∑ p ∈ C, suzukiVProduct S x *
        (S.nu p * R p * H (log (D : ℝ) / log p)) := by
      apply sum_le_sum
      intro p hp
      have hpv := (hcarrier p hp).2
      have hpEuler := suzukiVProduct_mul_localRatio_eq_sourceDiscreteEuler S (hpv.trans_le hvx)
      have hh := mul_le_mul_of_nonneg_left (hinner p hp) (hnu p (hsub hp))
      rw [← hpEuler, ← hR p] at hh
      nlinarith only [hh]
    _ = suzukiVProduct S x * (∑ p ∈ C, S.nu p * R p * H (log (D : ℝ) / log p)) :=
      (mul_sum _ _ _).symm
    _ ≤ suzukiVProduct S x * (∑ p ∈ P, S.nu p * R p * H (log (D : ℝ) / log p)) := by
      apply mul_le_mul_of_nonneg_left _ hV
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      exact mul_nonneg (mul_nonneg (hnu p hp) (hR0 p)) (hH0 p hp)
    _ = _ := rfl

#print axioms actual_source_successor_atom_bound
end ChenEffective
