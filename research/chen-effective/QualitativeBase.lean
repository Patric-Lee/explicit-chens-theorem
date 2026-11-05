import QualitativeGoldbach

noncomputable section
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem qualitative_base_candidates {N : ℕ}
    (hGeom : qualitativeGeometryThreshold ≤ N)
    (hMass : sourceMassThreshold baseCandidateBudget ≤ N)
    (hDist : baseDistributionNumericalThreshold (60*baseCandidateBudget) baseCandidateBudget ≤ N)
    (hEven : Even N) :
    (jurkatRichertBaseMainCoefficient jurkatRichertJ-1/40)*
        (SingularSeries.liuSingularSeries N*N/log (N : ℝ)^2) ≤
      ((jurkatRichertSourceCandidates N).card : ℝ) := by
  obtain ⟨hN2,hz2⟩ := qualitative_endpoint_parameters hGeom
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : log (N : ℝ) ≠ 0 := (log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  let S := jurkatRichertSourceBoundingSieve N
  let X : ℝ := (N : ℝ)^(1/2-baseCandidateEpsilon)
  let z : ℝ := (N : ℝ)^(1/10 : ℝ)
  let s := qualitativeRatio S X z
  let D := qualitativeLevel S X
  let Z := ⌈(D : ℝ)^(1/s)⌉₊
  have hX : 0 < X := Real.rpow_pos_of_pos hN0 _
  have hshift := qualitative_ratio_shift S hGeom hX
  have heq : log X/log z = 5-10*baseCandidateEpsilon := by
    dsimp only [X,z]
    rw [log_rpow hN0, log_rpow hN0]
    field_simp; ring
  change 0 ≤ log X/log z-s ∧ log X/log z-s ≤ 1/10^7 at hshift
  rw [heq] at hshift
  have hs4 : 4 ≤ s := by
    norm_num [baseCandidateEpsilon,lowerSieveEpsilon,baseCandidateBudget] at hshift
    linarith only [hshift.2]
  have hs5 : s ≤ 5 := by
    norm_num [baseCandidateEpsilon,lowerSieveEpsilon,baseCandidateBudget] at hshift
    linarith only [hshift.1]
  have hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z := by
    intro p hp
    exact (prime_dvd_jurkatRichertSourceSiftingProduct (Nat.prime_of_mem_primeFactors hp)).mp
      (Nat.dvd_of_mem_primeFactors hp) |>.2.1
  obtain ⟨hD,hZD,hZcut⟩ := qualitative_goldbach_geometry S hz2 hX rfl
    (by linarith only [hs4] : 3/2 ≤ s) hcut
  have hmass0 : 0 ≤ S.totalMass :=
    LiuWeight.liuLogarithmicIntegral_nonneg (2/log 2) (by positivity) (by exact_mod_cast hN2)
  have hfinite := preSieveCounting_lower_bound S powerPresieveStart hmass0
    (by norm_num [qualitativeSieveError]) (by norm_num [qualitativeSieveError])
    (qualitative_source_relative N) D Z hD hs4 hs5 rfl hZD hZcut
  have hrem0 := qualitative_remainder_base hGeom hz2
  have hf := numerical_lower_factor_near_five hs4 hs5
  rw [dimensionOneLowerLinearSieveFactor_five] at hf
  let A := jurkatRichertBaseSieveFactor jurkatRichertJ
  let B := jurkatRichertMertensFactor
  let t : ℝ := 1/baseCandidateBudget
  let M : ℝ := SingularSeries.liuSingularSeries N*N/log (N : ℝ)^2
  have ht : t=(1/20000000 : ℝ) := by norm_num [t,baseCandidateBudget]
  obtain ⟨hAlo,hAhi,hBhi⟩ := numerical_base_factor_caps
  have hAt : 0 ≤ A-1/1000 := by dsimp [A]; linarith only [hAlo]
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
  have hV0 : 0 ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    exact prod_nonneg (fun p hp => (sub_pos.mpr (S.nu_lt_one_of_prime p
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))).le)
  have hcoef0 : A-1/1000 ≤ dimensionOneLowerLinearSieveFactor s-6000*qualitativeSieveError := by
    norm_num [baseCandidateEpsilon,lowerSieveEpsilon,baseCandidateBudget] at hshift
    dsimp only [A]
    norm_num only [qualitativeSieveError] at *
    linarith only [hf,hshift.2]
  have hcount : (A-1/1000)*(S.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S)-
      jurkatRichertSourceRemainderSum N baseCandidateEpsilon ≤ S.siftedSum := by
    have hh := mul_le_mul_of_nonneg_left hcoef0 (mul_nonneg hmass0 hV0)
    dsimp only [D,X,Z,s,z,S] at hfinite hrem0 hh ⊢
    nlinarith only [hh,hfinite,hrem0]
  have hr : 0 < baseCandidateBudget := by norm_num [baseCandidateBudget]
  have hrem : jurkatRichertSourceRemainderSum N baseCandidateEpsilon ≤ t*M := by
    have h := numerical_base_distribution (m := 60*baseCandidateBudget)
      (by norm_num [baseCandidateBudget]) hr hDist hEven
    simpa only [baseCandidateEpsilon,lowerSieveEpsilon,Nat.cast_mul,Nat.cast_ofNat,mul_div_assoc,mul_assoc,t,M] using h
  have hmass : (B-40*t)*M ≤ S.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    have h := numerical_source_mass_lower hr hMass hEven
    convert h using 1
    dsimp [B,t,M,S,jurkatRichertMertensFactor]
    ring
  have hpaid := mul_le_mul_of_nonneg_left hmass hAt
  have hab : A*B=jurkatRichertBaseMainCoefficient jurkatRichertJ := jurkatRichert_sieveFactor_mul_mertensFactor
  have hcoef : jurkatRichertBaseMainCoefficient jurkatRichertJ-1/40 ≤ (A-1/1000)*(B-40*t)-t := by
    rw [← hab,ht]
    dsimp only [A,B] at *
    nlinarith only [hAhi,hBhi]
  have htarget := mul_le_mul_of_nonneg_right hcoef hM0
  have hbound : (jurkatRichertBaseMainCoefficient jurkatRichertJ-1/40)*M ≤ S.siftedSum := by
    nlinarith only [htarget,hpaid,hcount,hrem]
  rw [jurkatRichertSourceBoundingSieve_siftedSum_eq_card N] at hbound
  exact hbound

#print axioms qualitative_base_candidates
end ChenEffective
