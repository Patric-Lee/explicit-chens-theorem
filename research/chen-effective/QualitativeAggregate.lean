import QualitativeMedium

noncomputable section
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem qualitative_medium_prime_aggregate {N : ℕ}
    (hGeom : qualitativeGeometryThreshold ≤ N)
    (hSum : mediumPrimeSumThreshold ≤ N)
    (hMass : sourceUpperMassThreshold mediumPrimeBudget ≤ N)
    (hDist : varyingNumericalThreshold (120*mediumPrimeBudget) mediumPrimeBudget ≤ N)
    (hEven : Even N) :
    jurkatRichertSourceMediumPrimeAggregate N ≤
      (jurkatRichertQ1MainCoefficient jurkatRichertK+1/2)*
        (SingularSeries.liuSingularSeries N*N/log (N : ℝ)^2) := by
  have hr : 0 < mediumPrimeBudget := by norm_num [mediumPrimeBudget]
  have hPair : primePairThreshold ≤ N := (le_max_left _ _).trans hSum
  obtain ⟨hN9,_,_,_⟩ := numerical_prime_pair_parameters hPair
  let Q := jurkatRichertSourceMediumPrimes N
  let D := (jurkatRichertSourceBoundingSieve N).totalMass*
    AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceBoundingSieve N)
  let P := ∑ q ∈ Q, jurkatRichertUpperLinearSieveFactor (jurkatRichertSourceUpperSieveRatio N q mediumPrimeEpsilon)/((q : ℝ)-1)
  let R := ∑ q ∈ Q, 1/((q : ℝ)-1)
  let t : ℝ := 1/1000
  let u : ℝ := 1/(mediumPrimeBudget : ℝ)
  let B := jurkatRichertMertensFactor
  let J := mediumPrimeIntegral
  let M : ℝ := SingularSeries.liuSingularSeries N*N/Real.log (N : ℝ)^2
  have ht : t=(1/1000 : ℝ) := rfl
  have hu : u=(1/1000000000000 : ℝ) := by norm_num [u,mediumPrimeBudget]
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hJ0 : 0 ≤ J := numerical_medium_integral_caps.1
  have hJ120 : J ≤ 120 := numerical_medium_integral_caps.2
  have hB20 : B ≤ 20 := numerical_base_factor_caps.2.2
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
    have hh := numerical_source_mass_upper hr hMass hEven
    simpa only [D,B,M,u,div_eq_mul_inv,one_mul] using hh
  have hP : P ≤ J+1/10000000 := numerical_medium_prime_shifted hSum
  have hR : R ≤ 22 := numerical_medium_prime_reciprocal hPair
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
    have hh := preSieve_varying_distribution (120*mediumPrimeBudget) mediumPrimeBudget N
      (by norm_num [mediumPrimeBudget]) hr hDist hEven
    simpa only [mediumPrimeEpsilon,Nat.cast_mul,Nat.cast_ofNat,u,M,mul_div_assoc,mul_assoc] using hh
  have hPR : P+t*R ≤ J+1/10000000+22*t := by
    have hh := mul_le_mul_of_nonneg_left hR ht0
    simpa only [mul_comm] using add_le_add hP hh
  have hscaled : (∑ q ∈ Q, (jurkatRichertSourceConditionedBoundingSieve N q).totalMass * ((jurkatRichertUpperLinearSieveFactor (jurkatRichertSourceUpperSieveRatio N q mediumPrimeEpsilon)+t)* AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceConditionedBoundingSieve N q))) ≤
      ((B+300*u)*(J+1/10000000+22*t))*M := by
    calc
      _ ≤ D*(P+t*R) := hmain
      _ ≤ D*(J+1/10000000+22*t) := mul_le_mul_of_nonneg_left hPR hD0
      _ ≤ ((B+300*u)*M)*(J+1/10000000+22*t) :=
        mul_le_mul_of_nonneg_right hD (by positivity)
      _ = _ := by ring
  have hcoef : (B+300*u)*(J+1/10000000+22*t)+u ≤ jurkatRichertQ1MainCoefficient jurkatRichertK+1/2 := by
    rw [← numerical_medium_integral_coefficient,ht,hu]
    change _ ≤ B*J+1/2
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
    have hh := qualitative_conditioned_count hGeom hq
    rw [jurkatRichertSourceConditionedBoundingSieve_siftedSum_eq_card] at hh
    convert hh using 1 <;> first | rfl | ring
  nlinarith only [hfinite,hscaled,hrem,hpay]

#print axioms qualitative_medium_prime_aggregate
end ChenEffective
