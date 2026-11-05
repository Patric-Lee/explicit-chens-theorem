import QualitativeBase
import NumericalSourceUpperMass

noncomputable section
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem qualitative_conditioned_count {N q : ℕ}
    (hGeom : qualitativeGeometryThreshold ≤ N) (hq : q ∈ jurkatRichertSourceMediumPrimes N) :
    (jurkatRichertSourceConditionedBoundingSieve N q).siftedSum ≤
      (jurkatRichertSourceConditionedBoundingSieve N q).totalMass *
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceConditionedBoundingSieve N q) *
        (jurkatRichertUpperLinearSieveFactor (jurkatRichertSourceUpperSieveRatio N q mediumPrimeEpsilon)+49/1000) +
      sieveRemainderBelow (jurkatRichertSourceConditionedBoundingSieve N q)
        (jurkatRichertSourceUpperLevel N q mediumPrimeEpsilon) := by
  obtain ⟨hN2,hz2⟩ := qualitative_endpoint_parameters hGeom
  have hN1 : 1 < N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hprime := (mem_filter.mp hq).2.1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hprime.pos
  have hqm : 0 < (q : ℝ)-1 := by
    have hh : (1 : ℝ) < q := by exact_mod_cast hprime.one_lt
    linarith only [hh]
  let S := jurkatRichertSourceConditionedBoundingSieve N q
  let X : ℝ := (N : ℝ)^(1/2-mediumPrimeEpsilon)/(q : ℝ)
  let z : ℝ := (N : ℝ)^(1/10 : ℝ)
  let s := qualitativeRatio S X z
  let t := jurkatRichertSourceUpperSieveRatio N q mediumPrimeEpsilon
  let D := qualitativeLevel S X
  let Z := ⌈(D : ℝ)^(1/s)⌉₊
  have hX : 0 < X := div_pos (Real.rpow_pos_of_pos hN0 _) hq0
  have hshift : 0 ≤ t-s ∧ t-s ≤ 1/10^7 := qualitative_ratio_shift S hGeom hX
  have ht := jurkatRichertSourceUpperSieveRatio_mem hN1 numerical_medium_epsilon.1 numerical_medium_epsilon.2 hq
  have hcoord := jurkatRichertSourceMediumPrime_log_mem hN1 hq
  have hteq : t=5-10*(log (q : ℝ)/log (N : ℝ))-10*mediumPrimeEpsilon := by
    dsimp only [t]
    rw [jurkatRichertSourceUpperSieveRatio_eq_zero_sub hN1 hprime.pos,
      jurkatRichertSourceUpperSieveRatio_zero hN1 hprime.pos]
  have hslo : 3/2 ≤ s := by
    rw [hteq] at hshift
    norm_num only [mediumPrimeEpsilon,mediumPrimeBudget] at hshift
    linarith only [hshift.2,hcoord.2]
  have hshi : s ≤ 4 := by linarith only [ht.2,hshift.1]
  have hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z := by
    intro p hp
    exact jurkatRichertSourceConditioned_primeFactor_le_cutoff N q p hp
  obtain ⟨hD,hZD,hZcut⟩ := qualitative_goldbach_geometry S hz2 hX rfl hslo hcut
  have hmass0 : 0 ≤ S.totalMass := div_nonneg
    (LiuWeight.liuLogarithmicIntegral_nonneg (2/log 2) (by positivity) (by exact_mod_cast hN2)) hqm.le
  have hfinite := sharp_preSieveCounting_upper_bound S budgetPresieveStart hmass0
    (by norm_num [qualitativeSieveError]) (by norm_num [qualitativeSieveError])
    (qualitative_conditioned_relative N q) D Z hD hslo hshi rfl hZD hZcut
  have hQD := qualitative_level_QD S hz2 hX hslo
  have hlevel : smallSievePrimeProduct S budgetPresieveStart*D ≤ jurkatRichertSourceUpperLevel N q mediumPrimeEpsilon := by
    have hh : smallSievePrimeProduct S budgetPresieveStart*D ≤ ⌊X⌋₊ :=
      Nat.le_floor (by simpa only [Nat.cast_mul] using hQD)
    exact hh.trans (Nat.le_succ _)
  have hrem := sieveRemainderBelow_mono S hlevel
  have hreg := numerical_upper_factor_regular (s := s) (t := t)
    ⟨by linarith only [hslo],hshi⟩ ⟨by linarith only [ht.1],ht.2⟩
  have habs : |s-t| ≤ 1/10^7 := by rw [abs_sub_comm,abs_of_nonneg hshift.1]; exact hshift.2
  have hhatScaled := mul_le_mul_of_nonneg_left (sieveHat_normalized_le_one s)
    (show 0 ≤ 4806*qualitativeSieveError by norm_num [qualitativeSieveError])
  have hcoef : jurkatRichertUpperLinearSieveFactor s+4806*qualitativeSieveError*exp 2*sieveHat s ≤
      jurkatRichertUpperLinearSieveFactor t+49/1000 := by
    have hh := (le_abs_self (jurkatRichertUpperLinearSieveFactor s-jurkatRichertUpperLinearSieveFactor t)).trans hreg.2.2
    norm_num only [qualitativeSieveError,mediumPrimeBudget] at *
    linarith only [hh,habs,hhatScaled]
  have hV0 : 0 ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    exact prod_nonneg (fun p hp => (sub_pos.mpr (S.nu_lt_one_of_prime p
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))).le)
  have hpaid := mul_le_mul_of_nonneg_left hcoef (mul_nonneg hmass0 hV0)
  dsimp only [D,Z,s,z,X,S,t] at hfinite hpaid hrem ⊢
  linarith only [hfinite,hpaid,hrem]

#print axioms qualitative_conditioned_count
end ChenEffective
