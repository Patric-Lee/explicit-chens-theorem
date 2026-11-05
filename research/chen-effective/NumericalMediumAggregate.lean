import NumericalMediumUpperDensity
import NumericalSourceUpperMass
import NumericalBaseCandidates
import NumericalPreSieveCutoff

noncomputable section
namespace ChenEffective
open Real Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
attribute [local irreducible] logPowerCutoff

def mediumPrimeAggregateThreshold : ℕ :=
  max mediumPrimeSumThreshold
    (max (sourceUpperMassThreshold mediumPrimeBudget)
      (max (mediumUpperDensityThreshold mediumPrimeBudget)
        (varyingNumericalThreshold (120*mediumPrimeBudget) mediumPrimeBudget)))

/-- The actual medium-prime aggregate with the literal Chen coefficient.
No density, normalization, prime-sum, or distribution premise remains. -/
theorem numerical_medium_prime_aggregate {N : ℕ}
    (hN : mediumPrimeAggregateThreshold ≤ N) (hEven : Even N) :
    jurkatRichertSourceMediumPrimeAggregate N ≤
      (jurkatRichertQ1MainCoefficient jurkatRichertK+1/20000)*
        (SingularSeries.liuSingularSeries N*N/Real.log (N : ℝ)^2) := by
  have hr : 0 < mediumPrimeBudget := by norm_num [mediumPrimeBudget]
  have hSum : mediumPrimeSumThreshold ≤ N := (le_max_left _ _).trans hN
  have hMass : sourceUpperMassThreshold mediumPrimeBudget ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hDensity : mediumUpperDensityThreshold mediumPrimeBudget ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hDist : varyingNumericalThreshold (120*mediumPrimeBudget) mediumPrimeBudget ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hPair : primePairThreshold ≤ N := (le_max_left _ _).trans hSum
  obtain ⟨hN9,_,_,_⟩ := numerical_prime_pair_parameters hPair
  let Q := jurkatRichertSourceMediumPrimes N
  let D := (jurkatRichertSourceBoundingSieve N).totalMass*
    AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceBoundingSieve N)
  let P := ∑ q ∈ Q, jurkatRichertUpperLinearSieveFactor (jurkatRichertSourceUpperSieveRatio N q mediumPrimeEpsilon)/((q : ℝ)-1)
  let R := ∑ q ∈ Q, 1/((q : ℝ)-1)
  let t : ℝ := 1/(mediumPrimeBudget : ℝ)
  let B := jurkatRichertMertensFactor
  let J := mediumPrimeIntegral
  let M : ℝ := SingularSeries.liuSingularSeries N*N/Real.log (N : ℝ)^2
  have ht : t=(1/1000000000000 : ℝ) := by norm_num [t,mediumPrimeBudget]
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
  have hD : D ≤ (B+300*t)*M := by
    have hh := numerical_source_mass_upper hr hMass hEven
    simpa only [D,B,M,t,div_eq_mul_inv,one_mul] using hh
  have hP : P ≤ J+1/10000000 := numerical_medium_prime_shifted hSum
  have hR : R ≤ 22 := numerical_medium_prime_reciprocal hPair
  have hmain : jurkatRichertSourceVaryingQMainSum N mediumPrimeEpsilon ≤ D*(P+t*R) := by
    calc
      _ ≤ ∑ q ∈ Q, (jurkatRichertSourceConditionedBoundingSieve N q).totalMass*
          ((jurkatRichertUpperLinearSieveFactor (jurkatRichertSourceUpperSieveRatio N q mediumPrimeEpsilon)+t)*
            AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceConditionedBoundingSieve N q)) := by
        unfold jurkatRichertSourceVaryingQMainSum
        apply sum_le_sum
        intro q hq
        have hprime := (mem_filter.mp hq).2.1
        have hqm : 0 < (q : ℝ)-1 := by
          have hq1 : (1 : ℝ) < q := by exact_mod_cast hprime.one_lt
          linarith only [hq1]
        have hmass0 : 0 ≤ (jurkatRichertSourceConditionedBoundingSieve N q).totalMass := div_nonneg hli0 hqm.le
        exact mul_le_mul_of_nonneg_left (numerical_conditioned_upper_density hr (by omega) hDensity hq) hmass0
      _ = _ := by
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
  have hrem : jurkatRichertSourceVaryingQRemainderSum N mediumPrimeEpsilon ≤ t*M := by
    have hh := numerical_varying_upper_distribution (120*mediumPrimeBudget) mediumPrimeBudget N
      (by norm_num [mediumPrimeBudget]) hr hDist hEven
    simpa only [mediumPrimeEpsilon,Nat.cast_mul,Nat.cast_ofNat,t,M,mul_div_assoc,mul_assoc] using hh
  have hPR : P+t*R ≤ J+1/10000000+22*t := by
    have hh := mul_le_mul_of_nonneg_left hR ht0
    linarith only [hh,hP]
  have hscaled : jurkatRichertSourceVaryingQMainSum N mediumPrimeEpsilon ≤
      ((B+300*t)*(J+1/10000000+22*t))*M := by
    calc
      _ ≤ D*(P+t*R) := hmain
      _ ≤ D*(J+1/10000000+22*t) := mul_le_mul_of_nonneg_left hPR hD0
      _ ≤ ((B+300*t)*M)*(J+1/10000000+22*t) :=
        mul_le_mul_of_nonneg_right hD (by positivity)
      _ = _ := by ring
  have hcoef : (B+300*t)*(J+1/10000000+22*t)+t ≤ jurkatRichertQ1MainCoefficient jurkatRichertK+1/20000 := by
    rw [← numerical_medium_integral_coefficient,ht]
    change _ ≤ B*J+1/20000
    nlinarith only [hB20,hJ120]
  have hpay := mul_le_mul_of_nonneg_right hcoef hM0
  have hfinite := jurkatRichertSourceMediumPrimeAggregate_le_main_add_remainder N mediumPrimeEpsilon (by omega) numerical_medium_epsilon.2
  nlinarith only [hfinite,hscaled,hrem,hpay]

def nLower : ℕ := preSieveGeometryThreshold

theorem nLower_eq : nLower=3^(3^20000) := preSieveGeometryThreshold_eq

theorem numerical_weighted_lower {N : ℕ} (hN : nLower ≤ N) (hEven : Even N) :
    (2.6407 : ℝ)*SingularSeries.liuSingularSeries N*N/Real.log (N : ℝ)^2 ≤ jurkatRichertWeightedCount N :=
  preSieve_weighted_lower hN hEven

#print axioms numerical_medium_prime_aggregate
#print axioms numerical_weighted_lower
end ChenEffective
