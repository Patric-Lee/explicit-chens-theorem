import BJSStudyGeometry
import NumericalBaseCandidates

noncomputable section
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

noncomputable def bjsStudySieveError : ℝ := 1/4000

theorem bjsStudy_source_relative (N : ℕ) :
    HasRelativeSieveProduct (preSieveCounting (jurkatRichertSourceBoundingSieve N)
      bjsStudyPresieveStart) bjsStudySieveError :=
  by
    apply bjsStudy_product_relative
    · intro p hp
      exact (prime_dvd_jurkatRichertSourceSiftingProduct (Nat.prime_of_mem_primeFactors hp)).mp
        (Nat.dvd_of_mem_primeFactors hp) |>.1
    · intro p hp
      exact AnalyticNumberTheory.Sieve.goldbachNu_apply_prime (Nat.prime_of_mem_primeFactors hp)

theorem bjsStudy_conditioned_relative (N q : ℕ) :
    HasRelativeSieveProduct (preSieveCounting (jurkatRichertSourceConditionedBoundingSieve N q)
      bjsStudyPresieveStart) bjsStudySieveError :=
  bjsStudy_source_relative N

/-- Exact rounded geometry for the contracted counting weights. -/
theorem bjsStudy_goldbach_geometry (S : BoundingSieve) {X z s : ℝ}
    (hz : 2 ≤ z) (hX : 0 < X) (hs : s = bjsStudyRatio S X z) (hslo : 3/2 ≤ s)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) :
    let D := bjsStudyLevel S X
    let Z := ⌈(D : ℝ)^(1/s)⌉₊
    1 < D ∧ Z ≤ D ∧
      (∀ p ∈ (preSieveCounting S bjsStudyPresieveStart).prodPrimes.primeFactors, p < Z) := by
  let Q := smallSievePrimeProduct S bjsStudyPresieveStart
  have hQ : (0 : ℝ) < Q := by
    exact_mod_cast Nat.pos_of_ne_zero
      (S.prodPrimes_squarefree.squarefree_of_dvd (smallSievePrimeProduct_dvd S bjsStudyPresieveStart)).ne_zero
  obtain ⟨hD,_,hroot,_⟩ := real_level_to_natCeil_geometry hz
    (div_pos hX (mul_pos (by norm_num) hQ)) hs hslo
  refine ⟨by dsimp [bjsStudyLevel, Q] at hD ⊢; omega, ?_, ?_⟩
  · apply Nat.ceil_le.mpr
    exact Real.rpow_le_self_of_one_le (by exact_mod_cast (show 1 ≤ bjsStudyLevel S X by dsimp [bjsStudyLevel]; omega))
      ((div_le_one (by linarith only [hslo] : 0 < s)).mpr (by linarith only [hslo]))
  · intro p hp
    have hp' : p ∈ (restrictSievePrimes S bjsStudyPresieveStart).prodPrimes.primeFactors := hp
    rw [restrictSievePrimes_primeFactors] at hp'
    exact Nat.lt_ceil.mpr ((hcut p (mem_filter.mp hp').1).trans_lt hroot)

theorem bjsStudy_remainder_base {N : ℕ} (hN : bjsStudyGeometryThreshold ≤ N)
    (hz : 2 ≤ (N : ℝ)^(1/10 : ℝ)) :
    sieveRemainderBelow (jurkatRichertSourceBoundingSieve N)
      (smallSievePrimeProduct (jurkatRichertSourceBoundingSieve N) bjsStudyPresieveStart *
        bjsStudyLevel (jurkatRichertSourceBoundingSieve N) ((N : ℝ)^(1/2-baseCandidateEpsilon))) ≤
    jurkatRichertSourceRemainderSum N baseCandidateEpsilon := by
  let S := jurkatRichertSourceBoundingSieve N
  have hN0 : (0 : ℝ) < N := by
    by_contra hh
    have hn : N=0 := by exact_mod_cast le_antisymm (le_of_not_gt hh) (Nat.cast_nonneg N)
    norm_num [hn] at hz
  have hX := Real.rpow_pos_of_pos hN0 (1/2-baseCandidateEpsilon)
  have hshift := bjsStudy_ratio_shift S hN hX
  have hlogN : log (N : ℝ) ≠ 0 := by
    have hh := bjsStudy_log_budget hN
    have hU : 0 < bjsStudyPresieveStart := by unfold bjsStudyPresieveStart; positivity
    nlinarith only [hh,hU]
  have heq : log ((N : ℝ)^(1/2-baseCandidateEpsilon))/log ((N : ℝ)^(1/10 : ℝ)) =
      5-10*baseCandidateEpsilon := by
    rw [log_rpow hN0, log_rpow hN0]
    field_simp; ring
  rw [heq] at hshift
  have hs : 3/2 ≤ bjsStudyRatio S ((N : ℝ)^(1/2-baseCandidateEpsilon)) ((N : ℝ)^(1/10 : ℝ)) := by
    norm_num [baseCandidateEpsilon, lowerSieveEpsilon, baseCandidateBudget] at hshift ⊢
    linarith only [hshift.2]
  have hQD := bjsStudy_level_QD S hz hX hs
  apply sum_le_sum_of_subset_of_nonneg
  · intro d hd
    refine mem_filter.mpr ⟨(mem_filter.mp hd).1, ?_⟩
    have hdlt : (d : ℝ) < (smallSievePrimeProduct S bjsStudyPresieveStart *
        bjsStudyLevel S ((N : ℝ)^(1/2-baseCandidateEpsilon)) : ℕ) := by
      exact_mod_cast (mem_filter.mp hd).2
    exact hdlt.le.trans (by simpa only [Nat.cast_mul] using hQD)
  · intro d _ _; exact abs_nonneg (S.rem d)

#print axioms bjsStudy_remainder_base
end ChenEffective
