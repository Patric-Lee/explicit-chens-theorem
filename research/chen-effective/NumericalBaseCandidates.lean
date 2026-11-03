import NumericalBaseDensity
import NumericalSourceMass
import NumericalBV
import NumericalLowerEndpoint

noncomputable section
namespace ChenEffective
open Real Set Finset MeasureTheory
open MathlibNt.SieveTheory
open LinearSieve SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def baseDistributionNumericalThreshold (m d : ℕ) : ℕ :=
  max (numericalBVThreshold 3) (lowerDistributionThreshold m d 1000344400000012180)

theorem numerical_base_distribution {m d N : ℕ} (hm : 3 ≤ m) (hd : 0 < d)
    (hN : baseDistributionNumericalThreshold m d ≤ N) (hEven : Even N) :
    jurkatRichertSourceRemainderSum N (1/(m : ℝ)) ≤
      (1/(d : ℝ))*SingularSeries.liuSingularSeries N*N/Real.log N^(2 : ℕ) := by
  apply explicit_base_distribution_from_BV m d 1000344400000012180 N hm hd
    ((le_max_right _ _).trans hN) hEven (numericalBVConstant 3)
    (by rw [numerical_BV_constant_three]; norm_num)
  exact numerical_BV 3 N ((le_max_left _ _).trans hN)

/-- This budget pays all three losses, without optimizing the small polynomial constants. -/
def baseCandidateBudget : ℕ := 20000000
def baseCandidateEpsilon : ℝ := lowerSieveEpsilon baseCandidateBudget
def baseCandidateThreshold : ℕ :=
  max (baseDensityThreshold (2*baseCandidateBudget))
    (max (sourceMassThreshold baseCandidateBudget)
      (baseDistributionNumericalThreshold (60*baseCandidateBudget) baseCandidateBudget))

theorem numerical_base_factor_caps :
    (2/5 : ℝ) ≤ jurkatRichertBaseSieveFactor jurkatRichertJ ∧
      jurkatRichertBaseSieveFactor jurkatRichertJ ≤ 10 ∧ jurkatRichertMertensFactor ≤ 20 := by
  have hJ : jurkatRichertJ ≤ 1 := by
    unfold jurkatRichertJ
    calc
      _ ≤ ∫ _u in (3 : ℝ)..4, (1 : ℝ) :=
        intervalIntegral.integral_mono_on (by norm_num)
          (numerical_outer_interval (by norm_num) (by norm_num) (by norm_num))
          intervalIntegrable_const (fun u hu => (numerical_outer_integrand hu).2)
      _ = 1 := by norm_num
  have hE0 : 1 ≤ Real.exp Real.eulerMascheroniConstant :=
    Real.one_le_exp (by linarith only [Real.one_half_lt_eulerMascheroniConstant])
  have hE3 : Real.exp Real.eulerMascheroniConstant ≤ 3 :=
    (Real.exp_le_exp.mpr (Real.eulerMascheroniConstant_lt_two_thirds.le.trans (by norm_num))).trans
      (Real.exp_one_lt_d9.le.trans (by norm_num))
  have hl1 : 1 ≤ Real.log (4 : ℝ) := one_le_log_three.trans
    (Real.log_le_log (by norm_num) (by norm_num))
  have hl3 : Real.log (4 : ℝ) ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith only [h]
  have hL1 : 1 ≤ Real.log 4+jurkatRichertJ := by linarith only [hl1,jurkatRichertJ_nonneg]
  have hL4 : Real.log 4+jurkatRichertJ ≤ 4 := by linarith only [hl3,hJ]
  have hlo := mul_le_mul hE0 hL1 (by norm_num : (0 : ℝ) ≤ 1) (Real.exp_pos _).le
  have hhi := mul_le_mul hE3 hL4 (by linarith only [hL1] : 0 ≤ Real.log 4+jurkatRichertJ) (by norm_num : (0 : ℝ) ≤ 3)
  have hneg : Real.exp (-Real.eulerMascheroniConstant) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith only [Real.one_half_lt_eulerMascheroniConstant])
  unfold jurkatRichertBaseSieveFactor jurkatRichertMertensFactor
  constructor
  · nlinarith only [hlo]
  · constructor <;> nlinarith only [hhi,hneg]

/-- The actual base-candidate lower bound. Every threshold constituent is a
closed numerical formula; no eventual or analytic input remains. -/
theorem numerical_base_candidates {N : ℕ} (hN : baseCandidateThreshold ≤ N) (hEven : Even N) :
    (jurkatRichertBaseMainCoefficient jurkatRichertJ-1/40000)*
        (SingularSeries.liuSingularSeries N*N/Real.log N^(2 : ℕ)) ≤
      ((jurkatRichertSourceCandidates N).card : ℝ) := by
  have hr : 0 < baseCandidateBudget := by norm_num [baseCandidateBudget]
  have hDens : baseDensityThreshold (2*baseCandidateBudget) ≤ N := (le_max_left _ _).trans hN
  have hMass : sourceMassThreshold baseCandidateBudget ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hDist : baseDistributionNumericalThreshold (60*baseCandidateBudget) baseCandidateBudget ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hDens
  obtain ⟨he0,he,_⟩ := numerical_lower_epsilon baseCandidateBudget hr
  let S := jurkatRichertSourceBoundingSieve N
  let D := jurkatRichertSourceLowerLevel N baseCandidateEpsilon
  let mu := jurkatRichertBaseLowerRosserWeight N baseCandidateEpsilon
  let A := jurkatRichertBaseSieveFactor jurkatRichertJ
  let B := jurkatRichertMertensFactor
  let t : ℝ := 1/baseCandidateBudget
  let M : ℝ := SingularSeries.liuSingularSeries N*N/Real.log N^(2 : ℕ)
  have ht : t = (1/20000000 : ℝ) := by norm_num [t,baseCandidateBudget]
  obtain ⟨hAlo,hAhi,hBhi⟩ := numerical_base_factor_caps
  have hAt : 0 ≤ A-t := by dsimp [A]; rw [ht]; linarith only [hAlo]
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
  have hmass0 : 0 ≤ S.totalMass :=
    LiuWeight.liuLogarithmicIntegral_nonneg (2/Real.log 2) (by positivity) (by exact_mod_cast hN2)
  have hcert : IsLowerRosserCertificate S.prodPrimes D :=
    jurkatRichertBaseLowerRosserWeight_certificate (by omega) (by change lowerSieveEpsilon baseCandidateBudget < 2/5; linarith only [he])
  have hfinite : S.totalMass*S.mainSum mu-lowerErrSum S D mu ≤ S.siftedSum :=
    mainSum_sub_lowerErrSum_le_siftedSum D mu hcert
      (lowerRosserWeight_hasLowerLevelSupport S.prodPrimes D)
  have hdensity := numerical_base_density_near_five hr hDens
  have hmain : (A-t)*(S.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S) ≤
      S.totalMass*S.mainSum mu := by
    have h := mul_le_mul_of_nonneg_left hdensity hmass0
    dsimp only [A,t,S,mu,baseCandidateEpsilon] at *
    nlinarith only [h]
  have herr : lowerErrSum S D mu ≤ jurkatRichertSourceRemainderSum N baseCandidateEpsilon :=
    jurkatRichertBaseLowerRosserError_le N baseCandidateEpsilon
  have hrem : jurkatRichertSourceRemainderSum N baseCandidateEpsilon ≤ t*M := by
    have h := numerical_base_distribution (m := 60*baseCandidateBudget) (by norm_num [baseCandidateBudget]) hr hDist hEven
    simpa only [baseCandidateEpsilon,lowerSieveEpsilon,Nat.cast_mul,Nat.cast_ofNat,mul_div_assoc,mul_assoc,t,M] using h
  have hmass : (B-40*t)*M ≤ S.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    have h := numerical_source_mass_lower hr hMass hEven
    convert h using 1
    dsimp [B,t,M,S,jurkatRichertMertensFactor]
    ring
  have hpaid := mul_le_mul_of_nonneg_left hmass hAt
  have hab : A*B = jurkatRichertBaseMainCoefficient jurkatRichertJ :=
    jurkatRichert_sieveFactor_mul_mertensFactor
  have hcoef : jurkatRichertBaseMainCoefficient jurkatRichertJ-1/40000 ≤ (A-t)*(B-40*t)-t := by
    rw [← hab,ht]
    dsimp only [A,B] at *
    nlinarith only [hAhi,hBhi]
  have htarget := mul_le_mul_of_nonneg_right hcoef hM0
  have hbound : (jurkatRichertBaseMainCoefficient jurkatRichertJ-1/40000)*M ≤ S.siftedSum := by
    nlinarith only [htarget,hpaid,hmain,hfinite,herr,hrem]
  rw [jurkatRichertSourceBoundingSieve_siftedSum_eq_card N] at hbound
  exact hbound

/-- Discharge the base hypothesis of the finite weighted-lower endpoint. -/
theorem numerical_lower_from_medium_prime_bound {N : ℕ}
    (hN : max baseCandidateThreshold lowerEndpointThreshold ≤ N) (hEven : Even N)
    (hUpper : jurkatRichertSourceMediumPrimeAggregate N ≤
      (jurkatRichertQ1MainCoefficient jurkatRichertK+1/20000)*
        (SingularSeries.liuSingularSeries N*N/Real.log N^(2 : ℕ))) :
    (2.6407 : ℝ)*SingularSeries.liuSingularSeries N*N/Real.log N^(2 : ℕ) ≤ jurkatRichertWeightedCount N :=
  numerical_lower_from_density_bounds ((le_max_right _ _).trans hN) hEven
    (numerical_base_candidates ((le_max_left _ _).trans hN) hEven) hUpper

#print axioms numerical_base_distribution
#print axioms numerical_base_candidates
#print axioms numerical_lower_from_medium_prime_bound
end ChenEffective
