import GRH14SourceMassCaps
import GRH14MediumDistribution
import GRH14LowerFactor
import GRH14RelativeProduct

noncomputable section
namespace ChenEffective.GRH14
open Real Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
variable [Fact HybridProduct.HybridPrefixWindow]
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem base_candidates_at_target {N : ℕ} (hN : targetCutoff   ≤   N) (hEven : Even N) :
    (jurkatRichertBaseMainCoefficient jurkatRichertJ-(3/50:ℝ))*
        (SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2)   ≤  
      ((jurkatRichertSourceCandidates N).card:ℝ) := by
  let S := jurkatRichertSourceBoundingSieve N
  let s := lowerRatio N 1
  let D := lowerLevel N 1
  let Z := Nat.ceil ((D:ℝ)^(1/s))
  let c := dimensionOneLowerLinearSieveFactor s-110*(1/2000:ℝ)*exp 2*sieveHat s
  let M := SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2
  let B := jurkatRichertMertensFactor
  let A := jurkatRichertBaseMainCoefficient jurkatRichertJ
  have hNbig := (lower_endpoint_parameters hN).1
  have hbase := lower_base_ratio hN
  have hslo : 4  ≤  s := by dsimp only [s]; linarith only [hbase.1]
  have hshi : s  ≤  5 := hbase.2
  obtain ⟨hD,hZD,hroot,hlevel⟩ := lower_level_geometry hN (q:=1) (by norm_num)
    (show 3/2  ≤  s by linarith only [hslo])
  have hDN : D  ≤  N := lower_level_le_endpoint hN (q:=1) (by norm_num) (by linarith only [hslo])
  have hcut : ∀ p ∈ (preSieveCounting S 4000000).prodPrimes.primeFactors, p<Z := by
    intro p hp
    change p∈(restrictSievePrimes S 4000000).prodPrimes.primeFactors at hp
    rw [restrictSievePrimes_primeFactors] at hp
    have hpf := (mem_filter.mp hp).1
    have hh := (prime_dvd_jurkatRichertSourceSiftingProduct (Nat.prime_of_mem_primeFactors hpf)).mp
      (Nat.dvd_of_mem_primeFactors hpf) |>.2.1
    exact Nat.lt_ceil.mpr (hh.trans_lt hroot)
  have hmass0 : 0  ≤  S.totalMass := LiuWeight.liuLogarithmicIntegral_nonneg (2/log 2)
    (by positivity) (by exact_mod_cast (show 2  ≤  N by omega))
  have hfinite := GRH.truncated_preSieveCounting_lower_bound S 4000000 hmass0
    (by norm_num : (0:ℝ)  ≤  1/4000) le_rfl (lower_source_relative N)
    D Z (preSieveTruncation N) (truncation_log_lower hN).1 hD hslo hshi rfl hZD hcut
  have hrem := base_truncated_remainder hN hEven (show 1  ≤  D by omega) hDN
    (by simpa only [Nat.one_mul] using hlevel)
  change GRH.truncatedRemainderBound S 4000000 D (preSieveTruncation N) ≤
    (3e-12:ℝ)*N/log (N:ℝ)^2 at hrem
  have hM0 : 0  ≤  M := by dsimp [M]; positivity [SingularSeries.liuSingularSeries_pos N]
  have hBpos : 0<B := by dsimp [B]; unfold jurkatRichertMertensFactor; positivity
  have hBmin : (1:ℝ)  ≤  B := mertens_factor_lower_one
  have hcoef : A-27/500  ≤  B*c := lower_density_budget hbase.1 hbase.2
  have hAmin : (2/5:ℝ)  ≤  A := by
    have hh := mul_le_mul_of_nonneg_right numerical_base_factor_caps.1 hBpos.le
    have hab := jurkatRichert_sieveFactor_mul_mertensFactor
    have hb := mul_le_mul_of_nonneg_left hBmin (by norm_num : (0:ℝ)  ≤  2/5)
    dsimp only [A,B] at *
    nlinarith only [hh,hab,hb]
  have hc0 : 0  ≤  c := by
    by_contra hh
    have hm := mul_neg_of_pos_of_neg hBpos (lt_of_not_ge hh)
    linarith only [hm,hcoef,hAmin]
  have hc6 : c  ≤  6 := by
    have hh := lower_factor_upper hslo hshi
    have hp : 0  ≤  110*(1/2000:ℝ)*exp 2*sieveHat s := by
      exact mul_nonneg (by positivity) (sieveHat_pos s).le
    dsimp only [c]
    linarith only [hh,hp]
  have hmass := (source_mass_at_target hN hEven).1
  change (B-1/500000)*M  ≤  S.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S at hmass
  have hpaid := mul_le_mul_of_nonneg_left hmass hc0
  have hcoefM := mul_le_mul_of_nonneg_right hcoef hM0
  have hcM := mul_le_mul_of_nonneg_right hc6 hM0
  have hremM : GRH.truncatedRemainderBound S 4000000 D (preSieveTruncation N)  ≤  (6e-12:ℝ)*M := by
    have hh := mul_le_mul_of_nonneg_right (half_le_liuSingularSeries N)
      (show 0  ≤  (6e-12:ℝ)*((N:ℝ)/log (N:ℝ)^2) by positivity)
    dsimp only [M]
    simp only [div_eq_mul_inv] at hrem hh ⊢
    nlinarith only [hrem,hh]
  have hcount : (A-3/50)*M  ≤  S.siftedSum := by
    change S.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S*c-
      GRH.truncatedRemainderBound S 4000000 D (preSieveTruncation N)  ≤  S.siftedSum at hfinite
    nlinarith only [hfinite,hpaid,hcoefM,hcM,hremM,hM0]
  rw [jurkatRichertSourceBoundingSieve_siftedSum_eq_card N] at hcount
  exact hcount

#print axioms base_candidates_at_target
end ChenEffective.GRH14
