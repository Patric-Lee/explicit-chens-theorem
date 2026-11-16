import BJSH30SourceMass
import BJSH30SourceUpperMass
/- Threshold-specialized companion to research/chen-bjs-study/BJSStudyAggregate.lean.
The original producer is retained. This companion rechecks its proof with
tighter numerical caps in the namespace ChenEffective.H30Conditional. -/
import BJSH30ConditionalMedium
import BJSH30ConditionalMediumReciprocal

noncomputable section
namespace ChenEffective.H30Conditional
open Real Set Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open H30 in
theorem preSieve_varying_paid (m d N : ℕ) (hm : 0 < m) (hd : 0< d) (hdcap : d≤10^7)
    (hN : distributionThreshold≤ N) (hBudget : m*highBVExponent (weightedSaving 6)≤3*10^11)
    (hEven : Even N) :
    preSieveVaryingRemainder N (1/(m:ℝ))≤
      (1/(d:ℝ))*SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2 := by
  have hw := weighted_distribution_paid m N hm hN hBudget
  obtain ⟨hN9,hl,hcut⟩ := distribution_parameters hN
  have hL := distribution_log hN
  have hN0 : (0:ℝ)< N := by exact_mod_cast (show 0< N by omega)
  have hp := log_pow_le_rpow_inv_explicit (k:=10) (m:=10) (by norm_num) (by norm_num) hcut
  have hc := numerical_varying_correction hN9 (show (0:ℝ)≤1/(m:ℝ) by positivity)
  have hc' : jurkatRichertSourceVaryingQUnconditionalCorrection N (1/(m:ℝ))≤
      3000*N/log (N:ℝ)^3 := by
    apply hc.trans
    apply (le_div_iff₀ (pow_pos hl 3)).mpr
    have he : (N:ℝ)^(9/10:ℝ)*(N:ℝ)^(1/10:ℝ)=N := by rw [← rpow_add hN0]; norm_num
    have hh := mul_le_mul_of_nonneg_left hp (show 0≤3000*(N:ℝ)^(9/10:ℝ) by positivity)
    norm_num only [Nat.cast_ofNat] at hh
    have he' : 3000*(N:ℝ)^(9/10:ℝ)*(N:ℝ)^(1/10:ℝ)=3000*N := by rw [mul_assoc,he]
    have ht : log (N:ℝ)^7*log (N:ℝ)^3=log (N:ℝ)^10 := by ring
    nlinarith only [hh,he',congrArg (fun x : ℝ => 3000*(N:ℝ)^(9/10:ℝ)*x) ht]
  have hpay : 3000*N/log (N:ℝ)^3≤(1/10^8:ℝ)*N/log (N:ℝ)^2 := by
    apply (div_le_div_iff₀ (pow_pos hl 3) (pow_pos hl 2)).mpr
    have hh := mul_le_mul_of_nonneg_right (show (3000:ℝ)≤(1/10^8:ℝ)*log (N:ℝ) by linarith only [hL])
      (show 0≤(N:ℝ)*log (N:ℝ)^2 by positivity)
    nlinarith only [hh]
  have hf := preSieve_unweighted_varying_remainder_le_BV N (1/(m:ℝ)) hEven (by omega)
  have hdR : (0:ℝ)< d := by exact_mod_cast hd
  have hdc : (d:ℝ)≤10^7 := by exact_mod_cast hdcap
  have hs := half_le_liuSingularSeries N
  have hcoef : (2/10^8:ℝ)≤(1/(d:ℝ))*SingularSeries.liuSingularSeries N := by
    rw [one_div,mul_comm,← div_eq_mul_inv]
    apply (le_div_iff₀ hdR).mpr
    linarith only [hs,hdc]
  have hmain := mul_le_mul_of_nonneg_right hcoef (show 0≤(N:ℝ)/log (N:ℝ)^2 by positivity)
  simp only [mul_div_assoc,mul_assoc] at hmain hw hpay hf hc' ⊢
  linarith only [hf,hw,hc',hpay,hmain]


theorem bjsStudy_medium_prime_aggregate {N : ℕ}
    (hGeom : bjsStudyGeometryThreshold ≤ N)
    (hSum : mediumPrimeSumThreshold ≤ N)
    (hMass : H30.sourceUpperMassThreshold mediumPrimeBudget ≤ N)
    (hDist : H30.distributionThreshold ≤ N)
    (hEven : Even N) :
    jurkatRichertSourceMediumPrimeAggregate N ≤
      (jurkatRichertQ1MainCoefficient jurkatRichertK+113/100)*
        (SingularSeries.liuSingularSeries N*N/log (N : ℝ)^2) := by
  have hr : 0 < mediumPrimeBudget := by norm_num [mediumPrimeBudget]
  have hPair : primePairThreshold ≤ N := hSum
  obtain ⟨hN9,_,_,_⟩ := numerical_prime_pair_parameters hPair
  let Q := jurkatRichertSourceMediumPrimes N
  let D := (jurkatRichertSourceBoundingSieve N).totalMass*
    AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceBoundingSieve N)
  let P := ∑ q ∈ Q, jurkatRichertUpperLinearSieveFactor (jurkatRichertSourceUpperSieveRatio N q mediumPrimeEpsilon)/((q : ℝ)-1)
  let R := ∑ q ∈ Q, 1/((q : ℝ)-1)
  let t : ℝ := 7/125
  let u : ℝ := 1/(mediumPrimeBudget : ℝ)
  let B := jurkatRichertMertensFactor
  let J := mediumPrimeIntegral
  let M : ℝ := SingularSeries.liuSingularSeries N*N/Real.log (N : ℝ)^2
  have ht : t=(7/125 : ℝ) := rfl
  have hu : u=(1/5000000 : ℝ) := by norm_num [u,mediumPrimeBudget]
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hJ0 : 0 ≤ J := numerical_medium_integral_caps.1
  have hJ120 : J ≤ 120 := numerical_medium_integral_caps.2
  have hB20 : B ≤ 25/2 := budget_mertens_factor_cap
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
  have hli0 : 0 ≤ (jurkatRichertSourceBoundingSieve N).totalMass :=
    LiuWeight.liuLogarithmicIntegral_nonneg (2/Real.log 2) (by positivity) (by exact_mod_cast (show 2 ≤ N by omega))
  have hV0 : 0 ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceBoundingSieve N) := by
    unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    exact prod_nonneg (fun p hp => sub_nonneg.mpr
      ((jurkatRichertSourceBoundingSieve N).nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp)
        ((Nat.mem_primeFactors_of_ne_zero (jurkatRichertSourceSiftingProduct_ne_zero N)).mp hp).2).le)
  have hD0 : 0 ≤ D := mul_nonneg hli0 hV0
  have hD : D ≤ (B+300*u)*M := by
    have hh := H30.numerical_source_mass_upper hr hMass hEven
    simpa only [D,B,M,u,div_eq_mul_inv,one_mul] using hh
  have hP : P ≤ J+1/10000 := numerical_medium_prime_shifted hSum
  have hR : R ≤ 8/5 := bjsStudy_medium_reciprocal hSum
  have hmain : (∑ q ∈ Q, (jurkatRichertSourceConditionedBoundingSieve N q).totalMass * ((jurkatRichertUpperLinearSieveFactor (jurkatRichertSourceUpperSieveRatio N q mediumPrimeEpsilon)+t)* AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceConditionedBoundingSieve N q))) ≤ D*(P+t*R) := by
    apply le_of_eq
    rw [show D*(P+t*R)=D*P+(D*t)*R by ring]
    dsimp only [D,P,R,Q]
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply sum_congr rfl
    intro q hq
    change (LiuWeight.liuLogarithmicIntegral (2/Real.log 2) N/((q : ℝ)-1))*
      ((jurkatRichertUpperLinearSieveFactor (jurkatRichertSourceUpperSieveRatio N q mediumPrimeEpsilon)+t)*
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceBoundingSieve N)) = _
    rw [show (jurkatRichertSourceBoundingSieve N).totalMass = LiuWeight.liuLogarithmicIntegral (2/Real.log 2) N from rfl]
    ring
  have hrem : preSieveVaryingRemainder N mediumPrimeEpsilon ≤ u*M := by
    have hh := preSieve_varying_paid 600000000 5000000 N
      (by norm_num) (by norm_num) (by norm_num) hDist
      (by norm_num [highBVExponent,weightedSaving,H30.weightedSaving]) hEven
    norm_num [mediumPrimeEpsilon,mediumPrimeBudget,u,M,mul_div_assoc,mul_assoc] at hh ⊢
    exact hh
  have hPR : P+t*R ≤ J+1/10000+(8/5)*t := by
    have hh := mul_le_mul_of_nonneg_left hR ht0
    simpa only [mul_comm] using add_le_add hP hh
  have hscaled : (∑ q ∈ Q, (jurkatRichertSourceConditionedBoundingSieve N q).totalMass * ((jurkatRichertUpperLinearSieveFactor (jurkatRichertSourceUpperSieveRatio N q mediumPrimeEpsilon)+t)* AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceConditionedBoundingSieve N q))) ≤
      ((B+300*u)*(J+1/10000+(8/5)*t))*M := by
    calc
      _ ≤ D*(P+t*R) := hmain
      _ ≤ D*(J+1/10000+(8/5)*t) := mul_le_mul_of_nonneg_left hPR hD0
      _ ≤ ((B+300*u)*M)*(J+1/10000+(8/5)*t) :=
        mul_le_mul_of_nonneg_right hD (by positivity)
      _ = _ := by ring
  have hcoef : (B+300*u)*(J+1/10000+(8/5)*t)+u ≤ jurkatRichertQ1MainCoefficient jurkatRichertK+113/100 := by
    rw [← numerical_medium_integral_coefficient,ht,hu]
    change _ ≤ B*J+113/100
    nlinarith only [hB20,hJ120]
  have hpay := mul_le_mul_of_nonneg_right hcoef hM0
  have hfinite : jurkatRichertSourceMediumPrimeAggregate N ≤
      (∑ q ∈ Q, (jurkatRichertSourceConditionedBoundingSieve N q).totalMass *
        ((jurkatRichertUpperLinearSieveFactor (jurkatRichertSourceUpperSieveRatio N q mediumPrimeEpsilon)+t)*
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceConditionedBoundingSieve N q))) +
      preSieveVaryingRemainder N mediumPrimeEpsilon := by
    unfold jurkatRichertSourceMediumPrimeAggregate preSieveVaryingRemainder
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro q hq
    have hh := bjsStudy_conditioned_count hGeom hq
    rw [jurkatRichertSourceConditionedBoundingSieve_siftedSum_eq_card] at hh
    convert hh using 1 <;> first | rfl | ring
  nlinarith only [hfinite,hscaled,hrem,hpay]

#print axioms bjsStudy_medium_prime_aggregate
end ChenEffective.H30Conditional
