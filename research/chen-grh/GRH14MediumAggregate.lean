import GRH14BaseCandidates
import GRH14MediumProfile

noncomputable section
namespace ChenEffective.GRH14
open Real Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
variable [Fact HybridProduct.HybridPrefixWindow]
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

theorem conditioned_sifted_upper {N q : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N)
    (hq : q∈jurkatRichertSourceMediumPrimes N) :
    (jurkatRichertSourceConditionedBoundingSieve N q).siftedSum ≤ (SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2)*
        (mediumUpperProfile (log (q:ℝ)/log (N:ℝ))/((q:ℝ)-1))+
      GRH.truncatedRemainderBound (jurkatRichertSourceConditionedBoundingSieve N q)
        4000000 (lowerLevel N q) (preSieveTruncation N) := by
  let S := jurkatRichertSourceConditionedBoundingSieve N q
  let S₀ := jurkatRichertSourceBoundingSieve N
  let s := lowerRatio N q
  let D := lowerLevel N q
  let Z := Nat.ceil ((D:ℝ)^(1/s))
  let c := jurkatRichertUpperLinearSieveFactor s+110*(1/2000:ℝ)*exp 2*sieveHat s
  let M := SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2
  let B := jurkatRichertMertensFactor
  have hNbig := (lower_endpoint_parameters hN).1
  have hqp := (mem_filter.mp hq).2.1
  have hq0 : (0:ℝ)<q := by exact_mod_cast hqp.pos
  have hqm : 0<(q:ℝ)-1 := by
    have hh : (1:ℝ)<q := by exact_mod_cast hqp.one_lt
    linarith only [hh]
  have hs := lower_medium_ratio hN hq
  obtain ⟨hD,hZD,hroot,hlevel⟩ := lower_level_geometry hN hqp.pos hs.1
  have hcut : ∀ p∈(preSieveCounting S 4000000).prodPrimes.primeFactors, p<Z := by
    intro p hp
    change p∈(restrictSievePrimes S 4000000).prodPrimes.primeFactors at hp
    rw [restrictSievePrimes_primeFactors] at hp
    have hh := jurkatRichertSourceConditioned_primeFactor_le_cutoff N q p (mem_filter.mp hp).1
    exact Nat.lt_ceil.mpr (hh.trans_lt hroot)
  have hmass0 : 0 ≤ S.totalMass := div_nonneg
    (LiuWeight.liuLogarithmicIntegral_nonneg (2/log 2) (by positivity)
      (by exact_mod_cast (show 2 ≤ N by omega))) hqm.le
  have hf := GRH.truncated_preSieveCounting_upper_bound S 4000000 hmass0
    (by norm_num : (0:ℝ) ≤ 1/4000) le_rfl (lower_conditioned_relative N q)
    D Z (preSieveTruncation N) (truncation_log_lower hN).1 hD hs.1 hs.2 rfl hZD hcut
  have hc0 : 0 ≤ c := by
    have hh := (numerical_upper_factor_regular ⟨by linarith only [hs.1],hs.2⟩
      ⟨by linarith only [hs.1],hs.2⟩).1
    have hp : 0 ≤ 110*(1/2000:ℝ)*exp 2*sieveHat s := mul_nonneg (by positivity) (sieveHat_pos s).le
    dsimp only [c]
    linarith only [hh,hp]
  have hmass := (source_mass_at_target hN hEven).2
  change S₀.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S₀ ≤ (B+3/200)*M at hmass
  have hcond : S.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S ≤ (B+3/200)*M/((q:ℝ)-1) := by
    have heq : S.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S =
        (S₀.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S₀)/((q:ℝ)-1) := by
      change ((S₀.totalMass/((q:ℝ)-1))*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S₀) =
        (S₀.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S₀)/((q:ℝ)-1)
      ring
    rw [heq]
    exact div_le_div_of_nonneg_right hmass hqm.le
  have hm := mul_le_mul_of_nonneg_right hcond hc0
  have ha := jurkatRichertSourceMediumPrime_log_mem (by omega : 1<N) hq
  have hshift := lower_ratio_shift hN hqp.pos
  have hp := medium_pointwise_budget ha hs.1 (by linarith only [hshift.1]) hshift.2
  change (B+3/200)*c ≤ mediumUpperProfile (log (q:ℝ)/log (N:ℝ)) at hp
  have hM0 : 0 ≤ M := by dsimp only [M]; positivity [SingularSeries.liuSingularSeries_pos N]
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hM0) hqm.le
  have hm' : S.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S*c ≤ M*(mediumUpperProfile (log (q:ℝ)/log (N:ℝ))/((q:ℝ)-1)) := by
    apply hm.trans
    convert hh using 1 <;> ring
  change S.siftedSum ≤ S.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S*c+
    GRH.truncatedRemainderBound S 4000000 D (preSieveTruncation N) at hf
  exact hf.trans (add_le_add hm' le_rfl)

theorem medium_aggregate_at_target {N : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N) :
    jurkatRichertSourceMediumPrimeAggregate N ≤ (jurkatRichertQ1MainCoefficient jurkatRichertK+(111/100:ℝ))*
        (SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2) := by
  let M := SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2
  let D := lowerLevel N
  let R := fun q => GRH.truncatedRemainderBound (jurkatRichertSourceConditionedBoundingSieve N q)
    4000000 (D q) (preSieveTruncation N)
  have hD : ∀ q∈jurkatRichertSourceMediumPrimes N, 1 ≤ D q := by
    intro q hq
    have hh := (lower_level_geometry hN (mem_filter.mp hq).2.1.pos (lower_medium_ratio hN hq).1).1
    change 1 < D q at hh
    omega
  have hDN : ∀ q∈jurkatRichertSourceMediumPrimes N, D q ≤ N := fun q hq =>
    lower_level_le_endpoint hN (mem_filter.mp hq).2.1.pos (lower_medium_ratio hN hq).1
  have hlevel : ∀ q∈jurkatRichertSourceMediumPrimes N,
      preSieveTruncation N*D q ≤ jurkatRichertSourceUpperLevel N q (1/500:ℝ) := fun q hq =>
    lower_level_in_source hN (mem_filter.mp hq).2.1.pos (lower_medium_ratio hN hq).1
  have hr := medium_truncated_remainders hN hEven D hD hDN hlevel
  change (∑ q∈jurkatRichertSourceMediumPrimes N, R q) ≤ (3e-12:ℝ)*N/log (N:ℝ)^2 at hr
  have hs := sum_le_sum (fun q (_ : q∈jurkatRichertSourceMediumPrimes N) =>
    conditioned_sifted_upper hN hEven ‹q∈jurkatRichertSourceMediumPrimes N›)
  have heq : (∑ q∈jurkatRichertSourceMediumPrimes N,
      (jurkatRichertSourceConditionedBoundingSieve N q).siftedSum)=jurkatRichertSourceMediumPrimeAggregate N := by
    unfold jurkatRichertSourceMediumPrimeAggregate
    apply sum_congr rfl
    intro q _
    exact jurkatRichertSourceConditionedBoundingSieve_siftedSum_eq_card N q
  rw [heq,sum_add_distrib,← mul_sum] at hs
  have hM0 : 0 ≤ M := by dsimp only [M]; positivity [SingularSeries.liuSingularSeries_pos N]
  have hp := mul_le_mul_of_nonneg_left (medium_profile_source_sum hN) hM0
  have hrM : (∑ q∈jurkatRichertSourceMediumPrimes N, R q) ≤ (6e-12:ℝ)*M := by
    have hh := mul_le_mul_of_nonneg_right (half_le_liuSingularSeries N)
      (show 0 ≤ (6e-12:ℝ)*((N:ℝ)/log (N:ℝ)^2) by positivity)
    dsimp only [M]
    simp only [div_eq_mul_inv] at hr hh ⊢
    nlinarith only [hr,hh]
  change jurkatRichertSourceMediumPrimeAggregate N ≤ _
  change jurkatRichertSourceMediumPrimeAggregate N ≤ M*(∑ q∈jurkatRichertSourceMediumPrimes N, mediumUpperProfile (log (q:ℝ)/log (N:ℝ))/((q:ℝ)-1))+
      ∑ q∈jurkatRichertSourceMediumPrimes N, R q at hs
  nlinarith only [hs,hp,hrM,hM0]

#print axioms medium_aggregate_at_target
end ChenEffective.GRH14
