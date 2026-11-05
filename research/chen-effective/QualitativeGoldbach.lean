import QualitativeGeometry
import NumericalBaseCandidates

noncomputable section
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

noncomputable def qualitativeSieveError : ℝ := 1/10000000

theorem qualitative_source_relative (N : ℕ) :
    HasRelativeSieveProduct (preSieveCounting (jurkatRichertSourceBoundingSieve N)
      powerPresieveStart) qualitativeSieveError :=
  restricted_source_relative N

theorem qualitative_conditioned_relative (N q : ℕ) :
    HasRelativeSieveProduct (preSieveCounting (jurkatRichertSourceConditionedBoundingSieve N q)
      powerPresieveStart) qualitativeSieveError :=
  restricted_conditioned_relative N q

/-- Exact rounded geometry for the contracted counting weights. -/
theorem qualitative_goldbach_geometry (S : BoundingSieve) {X z s : ℝ}
    (hz : 2 ≤ z) (hX : 0 < X) (hs : s = qualitativeRatio S X z) (hslo : 3/2 ≤ s)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) :
    let D := qualitativeLevel S X
    let Z := ⌈(D : ℝ)^(1/s)⌉₊
    1 < D ∧ Z ≤ D ∧
      (∀ p ∈ (preSieveCounting S powerPresieveStart).prodPrimes.primeFactors, p < Z) := by
  let Q := smallSievePrimeProduct S powerPresieveStart
  have hQ : (0 : ℝ) < Q := by
    exact_mod_cast Nat.pos_of_ne_zero
      (S.prodPrimes_squarefree.squarefree_of_dvd (smallSievePrimeProduct_dvd S powerPresieveStart)).ne_zero
  obtain ⟨hD,_,hroot,_⟩ := real_level_to_natCeil_geometry hz
    (div_pos hX (mul_pos (by norm_num) hQ)) hs hslo
  refine ⟨by dsimp [qualitativeLevel, Q] at hD ⊢; omega, ?_, ?_⟩
  · apply Nat.ceil_le.mpr
    exact Real.rpow_le_self_of_one_le (by exact_mod_cast (show 1 ≤ qualitativeLevel S X by dsimp [qualitativeLevel]; omega))
      ((div_le_one (by linarith only [hslo] : 0 < s)).mpr (by linarith only [hslo]))
  · intro p hp
    have hp' : p ∈ (restrictSievePrimes S powerPresieveStart).prodPrimes.primeFactors := hp
    rw [restrictSievePrimes_primeFactors] at hp'
    exact Nat.lt_ceil.mpr ((hcut p (mem_filter.mp hp').1).trans_lt hroot)

theorem qualitative_remainder_base {N : ℕ} (hN : qualitativeGeometryThreshold ≤ N)
    (hz : 2 ≤ (N : ℝ)^(1/10 : ℝ)) :
    sieveRemainderBelow (jurkatRichertSourceBoundingSieve N)
      (smallSievePrimeProduct (jurkatRichertSourceBoundingSieve N) powerPresieveStart *
        qualitativeLevel (jurkatRichertSourceBoundingSieve N) ((N : ℝ)^(1/2-baseCandidateEpsilon))) ≤
    jurkatRichertSourceRemainderSum N baseCandidateEpsilon := by
  let S := jurkatRichertSourceBoundingSieve N
  have hN0 : (0 : ℝ) < N := by
    by_contra hh
    have hn : N=0 := by exact_mod_cast le_antisymm (le_of_not_gt hh) (Nat.cast_nonneg N)
    norm_num [hn] at hz
  have hX := Real.rpow_pos_of_pos hN0 (1/2-baseCandidateEpsilon)
  have hshift := qualitative_ratio_shift S hN hX
  have hlogN : log (N : ℝ) ≠ 0 := by
    have hh := qualitative_log_budget hN
    have hU : 0 < powerPresieveStart := by unfold powerPresieveStart; positivity
    nlinarith only [hh,hU]
  have heq : log ((N : ℝ)^(1/2-baseCandidateEpsilon))/log ((N : ℝ)^(1/10 : ℝ)) =
      5-10*baseCandidateEpsilon := by
    rw [log_rpow hN0, log_rpow hN0]
    field_simp; ring
  rw [heq] at hshift
  have hs : 3/2 ≤ qualitativeRatio S ((N : ℝ)^(1/2-baseCandidateEpsilon)) ((N : ℝ)^(1/10 : ℝ)) := by
    norm_num [baseCandidateEpsilon, lowerSieveEpsilon, baseCandidateBudget] at hshift ⊢
    linarith only [hshift.2]
  have hQD := qualitative_level_QD S hz hX hs
  apply sum_le_sum_of_subset_of_nonneg
  · intro d hd
    refine mem_filter.mpr ⟨(mem_filter.mp hd).1, ?_⟩
    have hdlt : (d : ℝ) < (smallSievePrimeProduct S powerPresieveStart *
        qualitativeLevel S ((N : ℝ)^(1/2-baseCandidateEpsilon)) : ℕ) := by
      exact_mod_cast (mem_filter.mp hd).2
    exact hdlt.le.trans (by simpa only [Nat.cast_mul] using hQD)
  · intro d _ _; exact abs_nonneg (S.rem d)

#print axioms qualitative_remainder_base
end ChenEffective
