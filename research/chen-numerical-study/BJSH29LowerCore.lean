import BJSHybridProductBridge
import NumericalPreSieveDistribution
import BJSH29Distribution
import NumericalBaseCandidates
import NumericalUpperFactor
import MathlibNt.SieveTheory.Switching.SourceSieve
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import NumericalGoldbachProduct
import BJSStudyAssembly
import NumericalSourceUpperMass
import NumericalLowerEndpoint
import Goldbach.Statement


/- Derived from generic proved-window product adapters; checked as new H29 proof source. -/
section

noncomputable section
namespace ChenEffective.H29Core
variable [Fact HybridProduct.HybridPrefixWindow]
open Real Finset
open MathlibNt.SieveTheory.SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- This generic counting proof takes a proved window as an explicit instance.
The concrete Platt-backed witness is supplied in BJSH29ConditionalChen. -/
theorem reciprocal_prefix_window : HybridProduct.HybridPrefixWindow :=
  Fact.out

noncomputable def bjsStudyPresieveStart : ℝ := 4000000

theorem bjsStudy_interval_product (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) (u z : ℝ)
    (hu : bjsStudyPresieveStart ≤ u) (huz : u ≤ z)
    (hinterval : ∀ p ∈ s, u ≤ (p : ℝ) ∧ (p : ℝ) < z) :
    (∏ p ∈ s, (1-1/((p : ℝ)-1))⁻¹) ≤ (1+(1/4000:ℝ))*(log z/log u) :=
  HybridProduct.hybrid_interval_product reciprocal_prefix_window s hs u z hu huz hinterval

theorem bjsStudy_presieved_product (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p)
    (hpresieve : ∀ p ∈ s, bjsStudyPresieveStart ≤ (p : ℝ))
    (u z : ℝ) (hu : 1 < u) (huz : u ≤ z)
    (hinterval : ∀ p ∈ s, u ≤ (p : ℝ) ∧ (p : ℝ) < z) :
    (∏ p ∈ s, (1-1/((p : ℝ)-1))⁻¹) ≤ (1+(1/4000:ℝ))*(log z/log u) := by
  by_cases hUu : bjsStudyPresieveStart ≤ u
  · exact bjsStudy_interval_product s hs u z hUu huz hinterval
  have huU : u ≤ bjsStudyPresieveStart := le_of_not_ge hUu
  have hlu : 0 < log u := log_pos hu
  have hlz : 0 < log z := log_pos (hu.trans_le huz)
  by_cases hzU : z ≤ bjsStudyPresieveStart
  · have hempty : s=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      linarith only [hpresieve p hp,(hinterval p hp).2,hzU]
    rw [hempty,Finset.prod_empty]
    have hr : 1 ≤ log z/log u := (le_div_iff₀ hlu).mpr
      (by simpa using log_le_log (by linarith only [hu] : 0 < u) huz)
    nlinarith only [hr,(by norm_num : (0:ℝ) ≤ 1/4000)]
  have hUz : bjsStudyPresieveStart ≤ z := le_of_not_ge hzU
  apply (bjsStudy_interval_product s hs bjsStudyPresieveStart z le_rfl hUz
    (fun p hp => ⟨hpresieve p hp,(hinterval p hp).2⟩)).trans
  apply mul_le_mul_of_nonneg_left _ (by linarith only [(by norm_num : (0:ℝ) ≤ 1/4000)])
  exact div_le_div_of_nonneg_left hlz.le hlu (log_le_log (by linarith only [hu] : 0 < u) huU)


theorem bjsStudy_product_relative (S : BoundingSieve)
    (hodd : ∀ p ∈ S.prodPrimes.primeFactors, 2 < p)
    (hnu : ∀ p ∈ S.prodPrimes.primeFactors, S.nu p=1/((p : ℝ)-1)) :
    HasRelativeSieveProduct (preSieveCounting S bjsStudyPresieveStart) (1/4000:ℝ) := by
  intro u z hu huz
  unfold suzukiLocalRatio
  change (∏ p ∈ (restrictSievePrimes S bjsStudyPresieveStart).prodPrimes.primeFactors.filter
    (fun p : ℕ => u ≤ (p : ℝ) ∧ (p : ℝ) < z), (1-S.nu p)⁻¹) ≤ _
  rw [restrictSievePrimes_primeFactors]
  let s := (S.prodPrimes.primeFactors.filter (fun p : ℕ => bjsStudyPresieveStart ≤ (p : ℝ))).filter
    (fun p : ℕ => u ≤ (p : ℝ) ∧ (p : ℝ) < z)
  have hs : ∀ p ∈ s, p.Prime ∧ 2 < p := by
    intro p hp
    have hP := (mem_filter.mp (mem_filter.mp hp).1).1
    exact ⟨Nat.prime_of_mem_primeFactors hP,hodd p hP⟩
  have hid : (∏ p ∈ s, (1-S.nu p)⁻¹) = ∏ p ∈ s, (1-1/((p : ℝ)-1))⁻¹ := by
    apply prod_congr rfl
    intro p hp
    rw [hnu p (mem_filter.mp (mem_filter.mp hp).1).1]
  change (∏ p ∈ s, (1-S.nu p)⁻¹) ≤ _
  rw [hid]
  exact bjsStudy_presieved_product s hs (fun _ hp => (mem_filter.mp (mem_filter.mp hp).1).2)
    u z hu huz (fun _ hp => (mem_filter.mp hp).2)


#print axioms bjsStudy_product_relative
end ChenEffective.H29Core

end
end

namespace ChenEffective.H29Core
noncomputable def baseCandidateEpsilon : ℝ := 1/300000000
end ChenEffective.H29Core

/- Derived from research/chen-numerical-study/proof-sources/H30Conditional/BJSH30ConditionalGeometry.lean; checked as new H29 proof source. -/
section
/- Threshold-specialized companion to research/chen-bjs-study/BJSStudyGeometry.lean.
The original producer is retained. This companion rechecks its proof with
tighter numerical caps in the namespace ChenEffective.H29Core. -/

noncomputable section
namespace ChenEffective.H29Core
open Real Set Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 512

theorem bjsStudy_small_prime_product_log (S : BoundingSieve) :
    log (smallSievePrimeProduct S bjsStudyPresieveStart : ℝ) ≤ 2*bjsStudyPresieveStart := by
  have hh := presieve_log_cost
    (S.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < bjsStudyPresieveStart))
    (show 0 ≤ bjsStudyPresieveStart by unfold bjsStudyPresieveStart; positivity)
    (fun p hp => ⟨Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1, (mem_filter.mp hp).2.le⟩)
  have hlog : log (4 : ℝ) ≤ 2 := by
    rw [show (4 : ℝ)=2^2 by norm_num, log_pow]; norm_num only [Nat.cast_ofNat]
    linarith only [log_two_lt_d9]
  have hc : (smallSievePrimeProduct S bjsStudyPresieveStart : ℝ) =
    ∏ p ∈ S.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < bjsStudyPresieveStart), (p : ℝ) := by
    simp only [smallSievePrimeProduct, Nat.cast_prod]
  rw [hc]
  exact hh.trans (mul_le_mul_of_nonneg_right hlog (by unfold bjsStudyPresieveStart; positivity))

def bjsStudyGeometryThreshold : ℕ := H29.distributionThreshold

theorem bjsStudyGeometryThreshold_eq : bjsStudyGeometryThreshold=3^(3*10^12) := by
  unfold bjsStudyGeometryThreshold H29.distributionThreshold
  rw [H29.distributionExponent_eq]

theorem bjsStudy_log_budget {N : ℕ} (hN : bjsStudyGeometryThreshold ≤ N) :
    300000*(1+2*bjsStudyPresieveStart) ≤ log (N : ℝ) := by
  have h := H29.distribution_log hN
  norm_num [bjsStudyPresieveStart] at *
  linarith only [h]

noncomputable def bjsStudyLevel (S : BoundingSieve) (X : ℝ) : ℕ :=
  ⌊X/(2*(smallSievePrimeProduct S bjsStudyPresieveStart : ℝ))⌋₊+1
noncomputable def bjsStudyRatio (S : BoundingSieve) (X z : ℝ) : ℝ :=
  log (X/(2*(smallSievePrimeProduct S bjsStudyPresieveStart : ℝ)))/log z

theorem bjsStudy_endpoint_parameters {N : ℕ} (hN : bjsStudyGeometryThreshold ≤ N) :
    2 ≤ N ∧ 2 ≤ (N : ℝ)^(1/10 : ℝ) := by
  have hh := bjsStudy_log_budget hN
  have hU : 0 < bjsStudyPresieveStart := by unfold bjsStudyPresieveStart; positivity
  have hL : 10^6 ≤ log (N : ℝ) := by
    norm_num [bjsStudyPresieveStart] at hh
    linarith only [hh]
  have hN2 : 2 ≤ N := by
    by_contra hn
    have hc : N=0 ∨ N=1 := by omega
    rcases hc with rfl | rfl <;> norm_num at hL
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  refine ⟨hN2, ?_⟩
  rw [rpow_def_of_pos hN0]
  rw [← exp_log (by norm_num : (0 : ℝ) < 2)]
  apply exp_le_exp.mpr
  nlinarith only [hL, log_two_lt_d9]

theorem bjsStudy_ratio_shift (S : BoundingSieve) {N : ℕ} (hN : bjsStudyGeometryThreshold ≤ N)
    {X : ℝ} (hX : 0 < X) :
    0 ≤ log X/log ((N : ℝ)^(1/10 : ℝ)) - bjsStudyRatio S X ((N : ℝ)^(1/10 : ℝ)) ∧
    log X/log ((N : ℝ)^(1/10 : ℝ)) - bjsStudyRatio S X ((N : ℝ)^(1/10 : ℝ)) ≤ 1/30000 := by
  let Q := smallSievePrimeProduct S bjsStudyPresieveStart
  have hQnat : 0 < Q := Nat.pos_of_ne_zero
    (S.prodPrimes_squarefree.squarefree_of_dvd (smallSievePrimeProduct_dvd S bjsStudyPresieveStart)).ne_zero
  have hQ : (0 : ℝ) < Q := by exact_mod_cast hQnat
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQnat
  have hlog := bjsStudy_log_budget hN
  have hU : 0 < bjsStudyPresieveStart := by unfold bjsStudyPresieveStart; positivity
  have hN0 : (0 : ℝ) < N := by
    by_contra hh
    have hzero : N=0 := by exact_mod_cast (le_antisymm (le_of_not_gt hh) (Nat.cast_nonneg N))
    simp only [hzero, Nat.cast_zero, log_zero] at hlog
    nlinarith only [hU, hlog]
  have hL : 0 < log (N : ℝ) := by nlinarith only [hlog, hU]
  have hqlog : 0 ≤ log (2*(Q : ℝ)) := log_nonneg (by linarith only [hQ1])
  have hqcap : log (2*(Q : ℝ)) ≤ 1+2*bjsStudyPresieveStart := by
    rw [log_mul (by norm_num) hQ.ne']
    have hh := bjsStudy_small_prime_product_log S
    change log (Q : ℝ) ≤ _ at hh
    linarith only [hh, log_two_lt_d9]
  unfold bjsStudyRatio
  rw [log_div hX.ne' (mul_pos (by norm_num) hQ).ne', log_rpow hN0]
  constructor
  · have hdiv := div_nonneg hqlog (show 0 ≤ (1/10 : ℝ)*log (N : ℝ) by positivity)
    convert hdiv using 1 <;> first | rfl | ring
  · have hdiv : log (2*(Q : ℝ))/((1/10 : ℝ)*log (N : ℝ)) ≤ 1/30000 :=
      H29.presieve_shift_payment hL hqcap (by nlinarith only [hlog])
    convert hdiv using 1; ring

/-- The contracted level preserves the original BV range, including the floor
rounding cost. -/
theorem bjsStudy_level_QD (S : BoundingSieve) {X z : ℝ} (hz : 2 ≤ z) (hX : 0 < X)
    (hs : 3/2 ≤ bjsStudyRatio S X z) :
    (smallSievePrimeProduct S bjsStudyPresieveStart * bjsStudyLevel S X : ℝ) ≤ X := by
  let Q := smallSievePrimeProduct S bjsStudyPresieveStart
  have hQnat : 0 < Q := Nat.pos_of_ne_zero
    (S.prodPrimes_squarefree.squarefree_of_dvd (smallSievePrimeProduct_dvd S bjsStudyPresieveStart)).ne_zero
  have hQ : (0 : ℝ) < Q := by exact_mod_cast hQnat
  have hΔ1 : (1 : ℝ) ≤ X/(2*(Q : ℝ)) := by
    have hlogz : 0 < log z := log_pos (by linarith only [hz])
    have hlogs : 0 < log (X/(2*(Q : ℝ))) := by
      have hh := (le_div_iff₀ hlogz).mp hs
      nlinarith only [hh, hlogz]
    exact (log_pos_iff (by positivity)).mp hlogs |>.le
  have hfloor := Nat.floor_le (show 0 ≤ X/(2*(Q : ℝ)) by positivity)
  have hxq : 2*(Q : ℝ) ≤ X := by simpa only [one_mul] using (le_div_iff₀ (by positivity : 0 < 2*(Q : ℝ))).mp hΔ1
  change (Q : ℝ) * ((⌊X/(2*(Q : ℝ))⌋₊ : ℕ)+1 : ℕ) ≤ X
  push_cast
  have he : (Q : ℝ)*(X/(2*(Q : ℝ)))=X/2 := by field_simp
  nlinarith only [mul_le_mul_of_nonneg_left hfloor hQ.le, hxq, he]

#print axioms bjsStudy_ratio_shift
#print axioms bjsStudy_level_QD
end ChenEffective.H29Core

end
end

/- Derived from research/chen-numerical-study/proof-sources/H30Conditional/BJSH30ConditionalGoldbach.lean; checked as new H29 proof source. -/
section
/- Threshold-specialized companion to research/chen-bjs-study/BJSStudyGoldbach.lean.
The original producer is retained. This companion rechecks its proof with
tighter numerical caps in the namespace ChenEffective.H29Core. -/

noncomputable section
namespace ChenEffective.H29Core
variable [Fact HybridProduct.HybridPrefixWindow]
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
end ChenEffective.H29Core

end
end

/- Derived from research/chen-numerical-study/proof-sources/H30Conditional/BJSH30ConditionalMediumPrimeGrid.lean; checked as new H29 proof source. -/
section
/- Threshold-specialized companion to research/chen-effective/NumericalMediumPrimeGrid.lean.
The original producer is retained. This companion rechecks its proof with
tighter numerical caps in the namespace ChenEffective.H29Core. -/

noncomputable section
namespace ChenEffective.H29Core
open Real Set Finset MeasureTheory
open MathlibNt.SieveTheory SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
attribute [local irreducible] logPowerCutoff

def primePairThreshold : ℕ := H29.distributionThreshold

theorem numerical_prime_pair_parameters {N : ℕ} (hN : primePairThreshold ≤ N) :
    9 ≤ N ∧ (10^12:ℝ) ≤ log (N:ℝ) ∧
      (logPowerCutoff 2:ℝ) ≤ (N:ℝ)^(1/10:ℝ) ∧
      (logPowerCutoff 2:ℝ) ≤ (N:ℝ)^(1/10:ℝ) :=
  H30.numerical_prime_pair_parameters (by have h := H29.distribution_log hN; linarith only [h])

theorem numerical_prime_pair_interval {N : ℕ} (hN : primePairThreshold ≤ N)
    {a b : ℝ} (ha : 1/10 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    PrimeReciprocalLogScale.primeReciprocalLogInterval N a b ≤
      log (b/a)+100/log (N:ℝ)^2 :=
  H30.numerical_prime_pair_interval (numerical_prime_pair_parameters hN).2.1 ha hab hb


theorem numerical_prime_interval_carrier (N : ℕ) (a b : ℝ) :
    (Finset.Ioc (MertensTheorem.rpowFloor N a) (MertensTheorem.rpowFloor N b)).filter Nat.Prime =
      (Finset.range (PrimeReciprocalLogScale.rpowFloor N b+1)).filter
        (fun p : ℕ => p.Prime ∧ (N : ℝ)^a < (p : ℝ) ∧ (p : ℝ) ≤ (N : ℝ)^b) := by
  ext p
  simp only [Finset.mem_filter,Finset.mem_Ioc,Finset.mem_range,Nat.lt_succ_iff,MertensTheorem.rpowFloor,
    PrimeReciprocalLogScale.rpowFloor,Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg N) a),
    Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) b)]
  tauto

theorem numerical_medium_profile_integrable {a b : ℝ} (ha : 1/10 ≤ a) (hab : a ≤ b) (hb : b ≤ 1/3) :
    IntervalIntegrable (fun x => mediumPrimeProfile x/x) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  apply ContinuousOn.div
  · apply (show ContinuousOn mediumPrimeProfile (Icc (1/10 : ℝ) (1/3)) from
      jurkatRichertUpperLinearSieveFactor_zeroEpsilon_continuousOn).mono
    intro x hx
    exact ⟨ha.trans hx.1,hx.2.trans hb⟩
  · exact continuousOn_id
  · intro x hx
    linarith only [ha,hx.1]

/-- A quantitative one-dimensional logarithmic Darboux cell. -/
theorem numerical_medium_prime_cell {N : ℕ} (hN : primePairThreshold ≤ N) {a b : ℝ}
    (ha : 1/10 ≤ a) (hab : a ≤ b) (hb : b ≤ 1/3) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N a b ≤
      (∫ x in a..b, mediumPrimeProfile x/x)+3600*(b-a)^2+
        192*(100/Real.log (N : ℝ)^2) := by
  obtain ⟨hN9,hlog,_,_⟩ := numerical_prime_pair_parameters hN
  have hL : 0 < Real.log (N : ℝ) := by linarith only [hlog]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ha0 : 0 < a := by linarith only [ha]
  have hb0 : 0 < b := ha0.trans_le hab
  let h := b-a
  let e := 100/Real.log (N : ℝ)^2
  have hh0 : 0 ≤ h := sub_nonneg.mpr hab
  have hh1 : h ≤ 1 := by dsimp [h]; linarith only [ha,hb]
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  obtain ⟨hf0,hf12,_⟩ := numerical_medium_profile ⟨ha,hab.trans hb⟩ ⟨ha,hab.trans hb⟩
  have htest : MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N a b ≤
      (mediumPrimeProfile a+180*h)*PrimeReciprocalLogScale.primeReciprocalLogInterval N a b := by
    unfold MertensTheorem.weightedPrimeReciprocalLogSum
    unfold PrimeReciprocalLogScale.primeReciprocalLogInterval
    rw [← numerical_prime_interval_carrier,Finset.mul_sum]
    apply sum_le_sum
    intro p hp
    obtain ⟨hpc,hprime⟩ := mem_filter.mp hp
    obtain ⟨hpa,hpb⟩ := MertensTheorem.mem_Ioc_rpowFloor_iff.mp hpc
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have halog := Real.log_le_log (Real.rpow_pos_of_pos hN0 a) hpa.le
    have hblog := Real.log_le_log hp0 hpb
    rw [Real.log_rpow hN0] at halog hblog
    have hpinterval : Real.log (p : ℝ)/Real.log (N : ℝ) ∈ Icc a b :=
      ⟨(le_div_iff₀ hL).mpr (by nlinarith only [halog]),(div_le_iff₀ hL).mpr hblog⟩
    have hdiff := (numerical_medium_profile
      ⟨ha.trans hpinterval.1,hpinterval.2.trans hb⟩ ⟨ha,hab.trans hb⟩).2.2
    have habs : |Real.log (p : ℝ)/Real.log (N : ℝ)-a| ≤ h := by
      rw [abs_of_nonneg (sub_nonneg.mpr hpinterval.1)]
      dsimp [h]
      linarith only [hpinterval.2]
    have hf : mediumPrimeProfile (Real.log (p : ℝ)/Real.log (N : ℝ)) ≤ mediumPrimeProfile a+180*h := by
      have h := (le_abs_self _).trans hdiff
      linarith only [h,habs]
    simpa only [mul_one_div] using div_le_div_of_nonneg_right hf hp0.le
  have hmass := numerical_prime_pair_interval hN ha hab (by linarith only [hb] : b ≤ 1)
  have htest' := htest.trans (mul_le_mul_of_nonneg_left hmass (show 0 ≤ mediumPrimeProfile a+180*h by positivity))
  have hlog0 : 0 ≤ Real.log (b/a) := Real.log_nonneg ((le_div_iff₀ ha0).mpr (by simpa using hab))
  have hlog10 : Real.log (b/a) ≤ 10*h := by
    have hh := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    have heq : b/a-1 = h/a := by dsimp [h]; field_simp
    apply hh.trans
    rw [heq]
    apply (div_le_iff₀ ha0).mpr
    nlinarith only [ha,mul_nonneg hh0 (sub_nonneg.mpr ha)]
  have hone : IntervalIntegrable (fun x : ℝ => 1/x) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact continuousOn_const.div continuousOn_id (by intro x hx; linarith only [ha,hx.1])
  have hIntegral : (mediumPrimeProfile a-180*h)*Real.log (b/a) ≤ ∫ x in a..b, mediumPrimeProfile x/x := by
    have hc := intervalIntegral.integral_mono_on hab (hone.const_mul (mediumPrimeProfile a-180*h))
      (numerical_medium_profile_integrable ha hab hb) (fun x hx => ?_)
    · rw [intervalIntegral.integral_const_mul,integral_one_div_of_pos ha0 hb0] at hc
      exact hc
    · have hdiff := (numerical_medium_profile ⟨ha,hab.trans hb⟩ ⟨ha.trans hx.1,hx.2.trans hb⟩).2.2
      have habs : |a-x| ≤ h := by
        rw [abs_of_nonpos (sub_nonpos.mpr hx.1)]
        dsimp [h]
        linarith only [hx.2]
      have hf : mediumPrimeProfile a-180*h ≤ mediumPrimeProfile x := by
        have hh := (le_abs_self _).trans hdiff
        linarith only [hh,habs]
      simpa only [mul_one_div] using div_le_div_of_nonneg_right hf (show 0 ≤ x by linarith only [ha,hx.1])
  have hmesh := mul_le_mul_of_nonneg_left hlog10 (show 0 ≤ 360*h by positivity)
  have he := mul_le_mul_of_nonneg_right (show mediumPrimeProfile a+180*h ≤ 192 by linarith only [hf12,hh1]) he0
  change _ ≤ _+3600*h^2+192*e
  change _ ≤ (mediumPrimeProfile a+180*h)*(Real.log (b/a)+e) at htest'
  nlinarith only [htest',hIntegral,hmesh,he]

def mediumPrimeGridPoint (n i : ℕ) : ℝ := 1/10+(7/30 : ℝ)*(i : ℝ)/n

theorem mediumPrimeGridPoint_mono {n : ℕ} (hn : 0 < n) : Monotone (mediumPrimeGridPoint n) := by
  intro i j hij
  unfold mediumPrimeGridPoint
  gcongr

theorem weightedPrimeLogSum_add {N : ℕ} {a b c : ℝ} (hN : 1 ≤ N) (hab : a ≤ b) (hbc : b ≤ c) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N a b+
      MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N b c =
      MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N a c := by
  unfold MertensTheorem.weightedPrimeReciprocalLogSum
  simp only [Finset.sum_filter]
  apply Finset.sum_Ioc_consecutive
  · exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hab)
  · exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hbc)

theorem numerical_medium_grid_partition {N n : ℕ} (hN : 1 ≤ N) (hn : 0 < n) (k : ℕ) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N
      (mediumPrimeGridPoint n 0) (mediumPrimeGridPoint n k) =
        ∑ i ∈ range k, MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N
          (mediumPrimeGridPoint n i) (mediumPrimeGridPoint n (i+1)) := by
  induction k with
  | zero => simp [MertensTheorem.weightedPrimeReciprocalLogSum]
  | succ k ih =>
    rw [Finset.sum_range_succ,← ih]
    exact (weightedPrimeLogSum_add hN (mediumPrimeGridPoint_mono hn (Nat.zero_le k))
      (mediumPrimeGridPoint_mono hn (Nat.le_succ k))).symm

#print axioms numerical_medium_prime_cell
end ChenEffective.H29Core

end
end

/- Derived from research/chen-numerical-study/proof-sources/H30Conditional/BJSH30ConditionalMediumPrimeSum.lean; checked as new H29 proof source. -/
section
/- Threshold-specialized companion to research/chen-effective/NumericalMediumPrimeSum.lean.
The original producer is retained. This companion rechecks its proof with
tighter numerical caps in the namespace ChenEffective.H29Core. -/

noncomputable section
namespace ChenEffective.H29Core
open Real Set Finset MeasureTheory
open MathlibNt.SieveTheory SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
attribute [local irreducible] logPowerCutoff

def mediumPrimeIntegral : ℝ := ∫ a in (1/10 : ℝ)..(1/3 : ℝ), mediumPrimeProfile a/a

theorem numerical_medium_integral_caps : 0 ≤ mediumPrimeIntegral ∧ mediumPrimeIntegral ≤ 120 := by
  have hf (a : ℝ) (ha : a ∈ Icc (1/10 : ℝ) (1/3)) :
      0 ≤ mediumPrimeProfile a/a ∧ mediumPrimeProfile a/a ≤ 120 := by
    have hh := numerical_medium_profile ha ha
    have ha0 : 0 < a := by linarith only [ha.1]
    exact ⟨div_nonneg hh.1 ha0.le,(div_le_iff₀ ha0).mpr (by linarith only [hh.2.1,ha.1])⟩
  constructor
  · exact intervalIntegral.integral_nonneg (by norm_num) (fun a ha => (hf a ha).1)
  · unfold mediumPrimeIntegral
    calc
      _ ≤ ∫ _a in (1/10 : ℝ)..(1/3 : ℝ), (120 : ℝ) := intervalIntegral.integral_mono_on
        (by norm_num) (numerical_medium_profile_integrable (by norm_num) (by norm_num) (by norm_num))
        intervalIntegrable_const (fun a ha => (hf a ha).2)
      _ ≤ 120 := by norm_num

theorem numerical_medium_integral_coefficient :
    jurkatRichertMertensFactor*mediumPrimeIntegral = jurkatRichertQ1MainCoefficient jurkatRichertK := by
  have hh : mediumPrimeIntegral = 2*Real.exp Real.eulerMascheroniConstant/5*(Real.log 8+jurkatRichertK/2) :=
    jurkatRichertUpperLinearSieveFactor_zeroEpsilon_integral
  rw [hh]
  unfold jurkatRichertMertensFactor jurkatRichertQ1MainCoefficient
  have he : Real.exp (-Real.eulerMascheroniConstant)*Real.exp Real.eulerMascheroniConstant=1 := by
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  calc
    _ = 8*(Real.exp (-Real.eulerMascheroniConstant)*Real.exp Real.eulerMascheroniConstant)*(Real.log 8+jurkatRichertK/2) := by ring
    _ = _ := by rw [he, mul_one]

theorem numerical_medium_prime_grid {N n : ℕ} (hN : primePairThreshold ≤ N) (hn : 0 < n) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N (1/10) (1/3) ≤
      mediumPrimeIntegral+196/(n : ℝ)+192*(n : ℝ)*(100/Real.log (N : ℝ)^2) := by
  obtain ⟨hN9,hlog,_,_⟩ := numerical_prime_pair_parameters hN
  let c := mediumPrimeGridPoint n
  let h : ℝ := (7/30 : ℝ)/n
  let e : ℝ := 100/Real.log (N : ℝ)^2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hstart : c 0 = 1/10 := by simp [c,mediumPrimeGridPoint]
  have hend : c n = 1/3 := by dsimp [c,mediumPrimeGridPoint]; field_simp; ring
  have hmono : Monotone c := mediumPrimeGridPoint_mono hn
  have hc (i : ℕ) (hi : i ≤ n) : c i ∈ Icc (1/10 : ℝ) (1/3) := by
    have h1 := hmono (Nat.zero_le i)
    have h2 := hmono hi
    rw [hstart] at h1
    rw [hend] at h2
    exact ⟨h1,h2⟩
  have hstep (i : ℕ) : c (i+1)-c i=h := by dsimp [c,h,mediumPrimeGridPoint]; push_cast; ring
  have hint (i : ℕ) (hi : i < n) : IntervalIntegrable (fun a => mediumPrimeProfile a/a) volume (c i) (c (i+1)) :=
    numerical_medium_profile_integrable (hc i (by omega)).1 (hmono (by omega)) (hc (i+1) (by omega)).2
  have hsum := Finset.sum_le_sum (s := range n) (fun i hi =>
    numerical_medium_prime_cell hN (hc i (by have h := mem_range.mp hi; omega)).1
      (hmono (by omega)) (hc (i+1) (by have h := mem_range.mp hi; omega)).2)
  have hpartition := numerical_medium_grid_partition (N := N) (by omega : 1 ≤ N) hn n
  have hI := intervalIntegral.sum_integral_adjacent_intervals hint
  change (∑ i ∈ range n, ∫ x in c i..c (i+1), mediumPrimeProfile x/x) = _ at hI
  rw [hstart,hend] at hI
  change _ = mediumPrimeIntegral at hI
  change MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N (c 0) (c n) = _ at hpartition
  rw [hstart,hend] at hpartition
  rw [← hpartition] at hsum
  simp only [hstep,
    Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hsum
  rw [hI] at hsum
  have heq : (n : ℝ)*(3600*h^2)=196/(n : ℝ) := by dsimp [h]; field_simp; ring
  simpa only [heq,mul_assoc,mul_left_comm,e] using hsum

theorem numerical_medium_prime_unshifted {N : ℕ} (hN : primePairThreshold ≤ N) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N (1/10) (1/3) ≤
      mediumPrimeIntegral+1/100000 := by
  have hh := numerical_medium_prime_grid (n := 100000000) hN (by norm_num)
  have hL := (numerical_prime_pair_parameters hN).2.1
  have hl : 0 < Real.log (N:ℝ) := by linarith only [hL]
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 10^12) hL 2
  have he : (192:ℝ)*100000000*(100/log (N:ℝ)^2) ≤ 1/1000000000 := by
    rw [show (192:ℝ)*100000000*(100/log (N:ℝ)^2) = (192*100000000*100)/log (N:ℝ)^2 by ring]
    apply (div_le_iff₀ (sq_pos_of_pos hl)).mpr
    linarith only [hs]
  norm_num only [Nat.cast_ofNat] at hh
  linarith only [hh,he]

#print axioms numerical_medium_prime_unshifted
end ChenEffective.H29Core

end
end

/- Derived from research/chen-numerical-study/proof-sources/H30Conditional/BJSH30ConditionalMediumPrimeShift.lean; checked as new H29 proof source. -/
section
/- Threshold-specialized companion to research/chen-effective/NumericalMediumPrimeShift.lean.
The original producer is retained. This companion rechecks its proof with
tighter numerical caps in the namespace ChenEffective.H29Core. -/

noncomputable section
namespace ChenEffective.H29Core
open Real Set Finset
open MathlibNt.SieveTheory SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def mediumPrimeBudget : ℕ := 5000000
def mediumPrimeEpsilon : ℝ := 1/(60*(mediumPrimeBudget : ℝ))
def mediumPrimeSumThreshold : ℕ := primePairThreshold

theorem medium_prime_root_cutoff : (mediumPrimeBudget+2)^10 ≤ mediumPrimeSumThreshold := by
  have hsmall : (mediumPrimeBudget+2)^10 ≤ (3:ℕ)^200 := by norm_num [mediumPrimeBudget]
  apply hsmall.trans
  change (3:ℕ)^200 ≤ H29.distributionThreshold
  unfold H29.distributionThreshold
  exact Nat.pow_le_pow_right (by norm_num)
    (by rw [H29.distributionExponent_eq]; norm_num)

theorem numerical_medium_epsilon : 0 < mediumPrimeEpsilon ∧ mediumPrimeEpsilon < 1/60 := by
  norm_num [mediumPrimeEpsilon,mediumPrimeBudget]

theorem numerical_medium_prime_shifted {N : ℕ} (hN : mediumPrimeSumThreshold ≤ N) :
    (∑ q ∈ jurkatRichertSourceMediumPrimes N,
      jurkatRichertUpperLinearSieveFactor (jurkatRichertSourceUpperSieveRatio N q mediumPrimeEpsilon)/((q : ℝ)-1)) ≤
        mediumPrimeIntegral+1/10000 := by
  have hPair : primePairThreshold ≤ N := hN
  obtain ⟨h9,_,_,_⟩ := numerical_prime_pair_parameters hPair
  let d : ℝ := 1/(mediumPrimeBudget : ℝ)
  have hd : 0 < d := by norm_num [d,mediumPrimeBudget]
  have hpert : 1/(1-6*mediumPrimeEpsilon) ≤ 1+d := by norm_num [mediumPrimeEpsilon,d,mediumPrimeBudget]
  have he0 := numerical_medium_epsilon.1
  have he := numerical_medium_epsilon.2
  have hcut : mediumPrimeBudget+1 ≤ jurkatRichertSourceZ N-1 := numerical_source_cutoff
    (by norm_num [mediumPrimeBudget]) (medium_prime_root_cutoff.trans hN)
  have hroot : (mediumPrimeBudget : ℝ)+1 ≤ (N : ℝ)^(1/10 : ℝ) := by
    have hh : ((mediumPrimeBudget+1 : ℕ) : ℝ) ≤ (jurkatRichertSourceZ N-1 : ℕ) := by exact_mod_cast hcut
    have hfloor : ((jurkatRichertSourceZ N-1 : ℕ) : ℝ) ≤ (N : ℝ)^(1/10 : ℝ) := by
      simpa only [jurkatRichertSourceZ,Nat.add_sub_cancel] using Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) (1/10 : ℝ))
    simpa only [Nat.cast_add,Nat.cast_one] using hh.trans hfloor
  have hsum : (∑ q ∈ jurkatRichertSourceMediumPrimes N,
      jurkatRichertUpperLinearSieveFactor (jurkatRichertSourceUpperSieveRatio N q mediumPrimeEpsilon)/((q : ℝ)-1)) ≤
        (1+d)^2*MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N (1/10) (1/3) := by
    have hterm (q : ℕ) (hq : q ∈ jurkatRichertSourceMediumPrimes N) :
        jurkatRichertUpperLinearSieveFactor (jurkatRichertSourceUpperSieveRatio N q mediumPrimeEpsilon)/((q : ℝ)-1) ≤
          (1+d)^2*(mediumPrimeProfile (Real.log (q : ℝ)/Real.log (N : ℝ))/(q : ℝ)) := by
      obtain ⟨_,hprime,hlo,_⟩ := mem_filter.mp hq
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hprime.pos
      have hq1 : (1 : ℝ) < q := by exact_mod_cast hprime.one_lt
      have hqm : 0 < (q : ℝ)-1 := by linarith only [hq1]
      have hqLarge : (mediumPrimeBudget : ℝ)+1 < q := hroot.trans_lt hlo
      have hinv : 1/((q : ℝ)-1) ≤ (1+d)/(q : ℝ) := by
        rw [div_le_div_iff₀ hqm hq0]
        norm_num [d,mediumPrimeBudget] at hqLarge ⊢
        have hqReal : (5000001 : ℝ) < q := by exact_mod_cast hqLarge
        linarith only [hqReal]
      have hlog := jurkatRichertSourceMediumPrime_log_mem (show 1 < N by omega) hq
      have hf0 := jurkatRichertUpperLinearSieveFactor_zeroEpsilon_nonneg hlog
      have hf := jurkatRichertUpperLinearSieveFactor_perturbation he0 he hlog
      have hratio : jurkatRichertSourceUpperSieveRatio N q mediumPrimeEpsilon =
          5-10*mediumPrimeEpsilon-10*(Real.log (q : ℝ)/Real.log (N : ℝ)) := by
        rw [jurkatRichertSourceUpperSieveRatio_eq_zero_sub (by omega : 1 < N) hprime.pos,
          jurkatRichertSourceUpperSieveRatio_zero (by omega : 1 < N) hprime.pos]
        ring
      rw [hratio]
      calc
        _ ≤ (1/(1-6*mediumPrimeEpsilon)*mediumPrimeProfile (Real.log (q : ℝ)/Real.log (N : ℝ)))/((q : ℝ)-1) := div_le_div_of_nonneg_right hf hqm.le
        _ ≤ ((1+d)*mediumPrimeProfile (Real.log (q : ℝ)/Real.log (N : ℝ)))/((q : ℝ)-1) := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpert hf0) hqm.le
        _ = ((1+d)*mediumPrimeProfile (Real.log (q : ℝ)/Real.log (N : ℝ)))*(1/((q : ℝ)-1)) := by ring
        _ ≤ ((1+d)*mediumPrimeProfile (Real.log (q : ℝ)/Real.log (N : ℝ)))*((1+d)/(q : ℝ)) :=
          mul_le_mul_of_nonneg_left hinv (mul_nonneg (by positivity) hf0)
        _ = _ := by ring
    calc
      _ ≤ ∑ q ∈ jurkatRichertSourceMediumPrimes N, (1+d)^2*(mediumPrimeProfile (Real.log (q : ℝ)/Real.log (N : ℝ))/(q : ℝ)) := sum_le_sum hterm
      _ = _ := by
        rw [jurkatRichertSourceMediumPrimes_eq_Ioc_rpowFloor (by omega : 1 ≤ N)]
        unfold MertensTheorem.weightedPrimeReciprocalLogSum
        rw [Finset.mul_sum]
  have htransfer := hsum.trans (mul_le_mul_of_nonneg_left (numerical_medium_prime_unshifted hPair) (sq_nonneg (1+d)))
  have hcap := numerical_medium_integral_caps.2
  have hcoef : (1+d)^2*(mediumPrimeIntegral+1/100000) ≤ mediumPrimeIntegral+1/10000 := by
    norm_num [d,mediumPrimeBudget]
    linarith only [hcap]
  exact htransfer.trans hcoef

#print axioms numerical_medium_prime_shifted
end ChenEffective.H29Core

end
end

/- Derived from research/chen-numerical-study/proof-sources/H30Conditional/BJSH30ConditionalMediumReciprocal.lean; checked as new H29 proof source. -/
section
/- Threshold-specialized companion to research/chen-bjs-study/BJSStudyMediumReciprocal.lean.
The original producer is retained. This companion rechecks its proof with
tighter numerical caps in the namespace ChenEffective.H29Core. -/

noncomputable section
namespace ChenEffective.H29Core
open Real Set Finset
open MathlibNt.SieveTheory SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- A direct bound on the actual medium-prime reciprocal mass. This replaces
the old factor 22 in the density-error payment. -/
theorem bjsStudy_medium_reciprocal {N : ℕ} (hN : mediumPrimeSumThreshold ≤ N) :
    (∑ q ∈ jurkatRichertSourceMediumPrimes N, 1/((q : ℝ)-1)) ≤ 8/5 := by
  have hPair : primePairThreshold ≤ N := hN
  obtain ⟨h9,hlog,_,_⟩ := numerical_prime_pair_parameters hPair
  have hcutN : (10+1)^10 ≤ N :=
    (Nat.pow_le_pow_left (by norm_num [mediumPrimeBudget] : 10+1 ≤ mediumPrimeBudget+2) 10).trans
      (medium_prime_root_cutoff.trans hN)
  have hcut := numerical_source_cutoff (by norm_num : 2 ≤ (10 : ℕ)) hcutN
  have hroot : (10 : ℝ) ≤ (N : ℝ)^(1/10 : ℝ) := by
    have hh : (10 : ℝ) ≤ (jurkatRichertSourceZ N-1 : ℕ) := by exact_mod_cast hcut
    apply hh.trans
    simpa only [jurkatRichertSourceZ,Nat.add_sub_cancel] using
      Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) (1/10 : ℝ))
  have hsum : (∑ q ∈ jurkatRichertSourceMediumPrimes N, 1/((q : ℝ)-1)) ≤
      (10/9)*PrimeReciprocalLogScale.primeReciprocalLogInterval N (1/10) (1/3) := by
    calc
      _ ≤ (10/9)*∑ q ∈ jurkatRichertSourceMediumPrimes N, 1/(q : ℝ) := by
        rw [Finset.mul_sum]
        apply sum_le_sum
        intro q hq
        have hq10 := hroot.trans_lt (mem_filter.mp hq).2.2.1
        have hq0 : (0 : ℝ) < q := by linarith only [hq10]
        have hqm : 0 < (q : ℝ)-1 := by linarith only [hq10]
        rw [show (10/9 : ℝ)*(1/(q : ℝ))=(10/9)/(q : ℝ) by ring,
          div_le_div_iff₀ hqm hq0]
        linarith only [hq10]
      _ = _ := by
        congr 1
        rw [jurkatRichertSourceMediumPrimes_eq_Ioc_rpowFloor (by omega : 1 ≤ N)]
        unfold PrimeReciprocalLogScale.primeReciprocalLogInterval
        rw [← numerical_prime_interval_carrier]
  have he : (100:ℝ)/log (N:ℝ)^2 ≤ 1/100 := by
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 10^12) hlog 2
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith only [hlog]))).mpr
    linarith only [hs]
  have hm := numerical_prime_pair_interval hPair (a := 1/10) (b := 1/3)
    (by norm_num) (by norm_num) (by norm_num)
  have hl : log ((1/3 : ℝ)/(1/10)) ≤ 7/5 := by
    have hh := log_le_log (by norm_num : (0 : ℝ) < (1/3 : ℝ)/(1/10))
      (show (1/3 : ℝ)/(1/10) ≤ 4 by norm_num)
    rw [show (4 : ℝ)=2^2 by norm_num,log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh,log_two_lt_d9]
  nlinarith only [hsum,hm,hl,he]

#print axioms bjsStudy_medium_reciprocal
end ChenEffective.H29Core

end
end

/- Derived from research/chen-numerical-study/proof-sources/H30Conditional/BJSH30ConditionalBase.lean; checked as new H29 proof source. -/
section
/- Threshold-specialized companion to research/chen-bjs-study/BJSStudyBase.lean.
The original producer is retained. This companion rechecks its proof with
tighter numerical caps in the namespace ChenEffective.H29Core. -/

noncomputable section
namespace ChenEffective.H29Core
variable [Fact HybridProduct.HybridPrefixWindow]
open Real Set Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem bjsStudy_base_candidates {N : ℕ}
    (hGeom : bjsStudyGeometryThreshold ≤ N)
    (hMass : H30.sourceMassThreshold baseCandidateBudget ≤ N)
    (hDist : H29.distributionThreshold ≤ N)
    (hEven : Even N) :
    (jurkatRichertBaseMainCoefficient jurkatRichertJ-1/20)*
        (SingularSeries.liuSingularSeries N*N/log (N : ℝ)^2) ≤
      ((jurkatRichertSourceCandidates N).card : ℝ) := by
  obtain ⟨hN2,hz2⟩ := bjsStudy_endpoint_parameters hGeom
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : log (N : ℝ) ≠ 0 := (log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  let S := jurkatRichertSourceBoundingSieve N
  let X : ℝ := (N : ℝ)^(1/2-baseCandidateEpsilon)
  let z : ℝ := (N : ℝ)^(1/10 : ℝ)
  let s := bjsStudyRatio S X z
  let D := bjsStudyLevel S X
  let Z := ⌈(D : ℝ)^(1/s)⌉₊
  have hX : 0 < X := Real.rpow_pos_of_pos hN0 _
  have hshift := bjsStudy_ratio_shift S hGeom hX
  have heq : log X/log z = 5-10*baseCandidateEpsilon := by
    dsimp only [X,z]
    rw [log_rpow hN0, log_rpow hN0]
    field_simp; ring
  change 0 ≤ log X/log z-s ∧ log X/log z-s ≤ 1/30000 at hshift
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
  obtain ⟨hD,hZD,hZcut⟩ := bjsStudy_goldbach_geometry S hz2 hX rfl
    (by linarith only [hs4] : 3/2 ≤ s) hcut
  have hmass0 : 0 ≤ S.totalMass :=
    LiuWeight.liuLogarithmicIntegral_nonneg (2/log 2) (by positivity) (by exact_mod_cast hN2)
  have hfinite := bjsStudy_preSieveCounting_lower_bound S bjsStudyPresieveStart hmass0
    (by norm_num [bjsStudySieveError]) (by norm_num [bjsStudySieveError])
    (bjsStudy_source_relative N) D Z hD hs4 hs5 rfl hZD hZcut
  have hrem0 := bjsStudy_remainder_base hGeom hz2
  have hf := numerical_lower_factor_near_five hs4 hs5
  rw [dimensionOneLowerLinearSieveFactor_five] at hf
  let A := jurkatRichertBaseSieveFactor jurkatRichertJ
  let B := jurkatRichertMertensFactor
  let t : ℝ := 1/baseCandidateBudget
  let M : ℝ := SingularSeries.liuSingularSeries N*N/log (N : ℝ)^2
  have ht : t=(1/20000000 : ℝ) := by norm_num [t,baseCandidateBudget]
  obtain ⟨hAlo,hAhi,_⟩ := numerical_base_factor_caps
  have hBhi := budget_mertens_factor_cap
  have hAt : 0 ≤ A-9/2500 := by dsimp [A]; linarith only [hAlo]
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
  have hV0 : 0 ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    exact prod_nonneg (fun p hp => (sub_pos.mpr (S.nu_lt_one_of_prime p
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))).le)
  have hs45 : 9/2 ≤ s := by
    norm_num [baseCandidateEpsilon,lowerSieveEpsilon,baseCandidateBudget] at hshift
    linarith only [hshift.2]
  have hhat := sharp_sieveHat_lower_window hs45
  have hhatScaled := mul_le_mul_of_nonneg_left hhat
    (show 0 ≤ 110*(1/2000:ℝ) by norm_num [bjsStudySieveError])
  have hcoef0 : A-9/2500 ≤ dimensionOneLowerLinearSieveFactor s-110*(1/2000:ℝ)*exp 2*sieveHat s := by
    norm_num [baseCandidateEpsilon,lowerSieveEpsilon,baseCandidateBudget] at hshift
    dsimp only [A]
    norm_num only [bjsStudySieveError] at *
    linarith only [hf,hshift.2,hhatScaled]
  have hcount : (A-9/2500)*(S.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S)-
      jurkatRichertSourceRemainderSum N baseCandidateEpsilon ≤ S.siftedSum := by
    have hh := mul_le_mul_of_nonneg_left hcoef0 (mul_nonneg hmass0 hV0)
    dsimp only [D,X,Z,s,z,S] at hfinite hrem0 hh ⊢
    nlinarith only [hh,hfinite,hrem0]
  have hr : 0 < baseCandidateBudget := by norm_num [baseCandidateBudget]
  have hrem : jurkatRichertSourceRemainderSum N baseCandidateEpsilon ≤ t*M := by
    have h := H29.fixed_base_distribution hDist hEven
    convert h using 1 <;>
      norm_num [baseCandidateEpsilon,lowerSieveEpsilon,baseCandidateBudget,t,M]
    ring
  have hmass : (B-40*t)*M ≤ S.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    have h := H30.numerical_source_mass_lower hr hMass hEven
    convert h using 1
    dsimp [B,t,M,S,jurkatRichertMertensFactor]
    ring
  have hpaid := mul_le_mul_of_nonneg_left hmass hAt
  have hab : A*B=jurkatRichertBaseMainCoefficient jurkatRichertJ := jurkatRichert_sieveFactor_mul_mertensFactor
  have hcoef : jurkatRichertBaseMainCoefficient jurkatRichertJ-1/20 ≤ (A-9/2500)*(B-40*t)-t := by
    rw [← hab,ht]
    dsimp only [A,B] at *
    nlinarith only [hAhi,hBhi]
  have htarget := mul_le_mul_of_nonneg_right hcoef hM0
  have hbound : (jurkatRichertBaseMainCoefficient jurkatRichertJ-1/20)*M ≤ S.siftedSum := by
    nlinarith only [htarget,hpaid,hcount,hrem]
  rw [jurkatRichertSourceBoundingSieve_siftedSum_eq_card N] at hbound
  exact hbound

#print axioms bjsStudy_base_candidates
end ChenEffective.H29Core

end
end

/- Derived from research/chen-numerical-study/proof-sources/H30Conditional/BJSH30ConditionalMedium.lean; checked as new H29 proof source. -/
section
/- Threshold-specialized companion to research/chen-bjs-study/BJSStudyMedium.lean.
The original producer is retained. This companion rechecks its proof with
tighter numerical caps in the namespace ChenEffective.H29Core. -/

noncomputable section
namespace ChenEffective.H29Core
variable [Fact HybridProduct.HybridPrefixWindow]
open Real Set Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem bjsStudy_conditioned_count {N q : ℕ}
    (hGeom : bjsStudyGeometryThreshold ≤ N) (hq : q ∈ jurkatRichertSourceMediumPrimes N) :
    (jurkatRichertSourceConditionedBoundingSieve N q).siftedSum ≤
      (jurkatRichertSourceConditionedBoundingSieve N q).totalMass *
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceConditionedBoundingSieve N q) *
        (jurkatRichertUpperLinearSieveFactor (jurkatRichertSourceUpperSieveRatio N q mediumPrimeEpsilon)+7/125) +
      sieveRemainderBelow (jurkatRichertSourceConditionedBoundingSieve N q)
        (jurkatRichertSourceUpperLevel N q mediumPrimeEpsilon) := by
  obtain ⟨hN2,hz2⟩ := bjsStudy_endpoint_parameters hGeom
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
  let s := bjsStudyRatio S X z
  let t := jurkatRichertSourceUpperSieveRatio N q mediumPrimeEpsilon
  let D := bjsStudyLevel S X
  let Z := ⌈(D : ℝ)^(1/s)⌉₊
  have hX : 0 < X := div_pos (Real.rpow_pos_of_pos hN0 _) hq0
  have hshift : 0 ≤ t-s ∧ t-s ≤ 1/30000 := bjsStudy_ratio_shift S hGeom hX
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
  obtain ⟨hD,hZD,hZcut⟩ := bjsStudy_goldbach_geometry S hz2 hX rfl hslo hcut
  have hmass0 : 0 ≤ S.totalMass := div_nonneg
    (LiuWeight.liuLogarithmicIntegral_nonneg (2/log 2) (by positivity) (by exact_mod_cast hN2)) hqm.le
  have hfinite := bjsStudy_preSieveCounting_upper_bound S bjsStudyPresieveStart hmass0
    (by norm_num [bjsStudySieveError]) (by norm_num [bjsStudySieveError])
    (bjsStudy_conditioned_relative N q) D Z hD hslo hshi rfl hZD hZcut
  have hQD := bjsStudy_level_QD S hz2 hX hslo
  have hlevel : smallSievePrimeProduct S bjsStudyPresieveStart*D ≤ jurkatRichertSourceUpperLevel N q mediumPrimeEpsilon := by
    have hh : smallSievePrimeProduct S bjsStudyPresieveStart*D ≤ ⌊X⌋₊ :=
      Nat.le_floor (by simpa only [Nat.cast_mul] using hQD)
    exact hh.trans (Nat.le_succ _)
  have hrem := sieveRemainderBelow_mono S hlevel
  have hreg := numerical_upper_factor_regular (s := s) (t := t)
    ⟨by linarith only [hslo],hshi⟩ ⟨by linarith only [ht.1],ht.2⟩
  have habs : |s-t| ≤ 1/30000 := by rw [abs_sub_comm,abs_of_nonneg hshift.1]; exact hshift.2
  have hhatScaled := mul_le_mul_of_nonneg_left (sieveHat_normalized_le_one s)
    (show 0 ≤ 110*(1/2000:ℝ) by norm_num [bjsStudySieveError])
  have hcoef : jurkatRichertUpperLinearSieveFactor s+110*(1/2000:ℝ)*exp 2*sieveHat s ≤
      jurkatRichertUpperLinearSieveFactor t+7/125 := by
    have hh := (le_abs_self (jurkatRichertUpperLinearSieveFactor s-jurkatRichertUpperLinearSieveFactor t)).trans hreg.2.2
    norm_num only [bjsStudySieveError,mediumPrimeBudget] at *
    linarith only [hh,habs,hhatScaled]
  have hV0 : 0 ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    exact prod_nonneg (fun p hp => (sub_pos.mpr (S.nu_lt_one_of_prime p
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))).le)
  have hpaid := mul_le_mul_of_nonneg_left hcoef (mul_nonneg hmass0 hV0)
  dsimp only [D,Z,s,z,X,S,t] at hfinite hpaid hrem ⊢
  linarith only [hfinite,hpaid,hrem]

#print axioms bjsStudy_conditioned_count
end ChenEffective.H29Core

end
end

/- Derived from research/chen-numerical-study/proof-sources/H30Conditional/BJSH30ConditionalAggregate.lean; checked as new H29 proof source. -/
section
/- Threshold-specialized companion to research/chen-bjs-study/BJSStudyAggregate.lean.
The original producer is retained. This companion rechecks its proof with
tighter numerical caps in the namespace ChenEffective.H29Core. -/

noncomputable section
namespace ChenEffective.H29Core
variable [Fact HybridProduct.HybridPrefixWindow]
open Real Set Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open H29 in
theorem preSieve_varying_paid (m d N : ℕ) (hm : 0 < m) (hd : 0< d) (hdcap : d≤10^7)
    (hN : distributionThreshold≤ N) (hBudget : m*highBVExponent (weightedSaving 6)≤10^11)
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
    (hDist : H29.distributionThreshold ≤ N)
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
    have hh := preSieve_varying_paid 300000000 5000000 N
      (by norm_num) (by norm_num) (by norm_num) hDist
      (by norm_num [highBVExponent,weightedSaving,H29.weightedSaving]) hEven
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
end ChenEffective.H29Core

end
end

/- Derived from research/chen-numerical-study/proof-sources/H30Conditional/BJSH30ConditionalChen.lean; checked as new H29 proof source. -/
section

noncomputable section
namespace ChenEffective.H29Core
variable [Fact HybridProduct.HybridPrefixWindow]
open Real Set Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 512

def chenCutoff : ℕ := H29.distributionThreshold

omit [Fact HybridProduct.HybridPrefixWindow] in
theorem chenCutoff_eq : chenCutoff = 3^(3*10^12) := bjsStudyGeometryThreshold_eq

omit [Fact HybridProduct.HybridPrefixWindow] in
theorem square_cutoff_le : H29.squareClosedThreshold ≤ chenCutoff := by
  unfold H29.squareClosedThreshold chenCutoff H29.distributionThreshold
  apply Nat.pow_le_pow_right (by norm_num)
  rw [H29.primePairPowerExponent_eq, H29.distributionExponent_eq]

omit [Fact HybridProduct.HybridPrefixWindow] in
theorem endpoint_cutoff_le : lowerEndpointThreshold ≤ chenCutoff := by
  unfold lowerEndpointThreshold
  apply max_le
  · apply le_trans (by norm_num : (2:ℕ)^110+1 ≤ 3^100)
    unfold chenCutoff H29.distributionThreshold
    exact Nat.pow_le_pow_right (by norm_num)
      (by rw [H29.distributionExponent_eq]; norm_num)
  · apply max_le
    · exact H29.distribution_log_cutoff (by norm_num)
    · unfold chenCutoff H29.distributionThreshold
      apply Nat.pow_le_pow_right (n:=3) (by decide)
      rw [H29.distributionExponent_eq]
      norm_num

/-- The lower count is assembled from the actual pre-sieved finite counts,
the proved distribution estimates, and the proved Platt-based reciprocal-prefix window. -/
theorem weighted_lower {N : ℕ} (hN : chenCutoff ≤ N) (hEven : Even N) :
    (2.02575:ℝ)*(SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2) ≤
      jurkatRichertWeightedCount N := by
  have hBase := bjsStudy_base_candidates hN
    ((H29.source_mass_caps (r:=baseCandidateBudget) (by norm_num [baseCandidateBudget])).1.trans
      (square_cutoff_le.trans hN)) hN hEven
  have hUpper := bjsStudy_medium_prime_aggregate hN hN
    ((H29.source_mass_caps (r:=mediumPrimeBudget) (by norm_num [mediumPrimeBudget])).2.trans
      (square_cutoff_le.trans hN)) hN hEven
  let M := SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2
  have hEnd := endpoint_cutoff_le.trans hN
  have hbig : 2^110 < N := by unfold lowerEndpointThreshold at hEnd; omega
  have hb := jurkatRichertSourceWeightedCount_sub_boundary_le_distinct N hbig hEven
  have hp := jurkatRichertDistinctWeightedCount_sub_proper_le N hbig hEven
  have he := numerical_lower_endpoint_loss hEnd
  have he' : 60*(N:ℝ)^(9/10:ℝ) ≤ (1/20000:ℝ)*M := by
    convert he using 1
    dsimp [M]
    ring
  have hn : 0 ≤ (N:ℝ)^(9/10:ℝ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hboundary : jurkatRichertSourceWeightedCount N ≤ jurkatRichertWeightedCount N+
      bjsStudyBudget.endpointLoss*M := by
    norm_num only [bjsStudyBudget] at *
    nlinarith only [hb,hp,he',hn]
  have hh := chen_budget_weighted bjsStudyBudget hBase hUpper hboundary
  convert hh using 1
  norm_num [bjsStudyBudget, ChenBudget.weighted]

/-- Conditional numerical Chen theorem at H=28.823681..., with the exact
cutoff 3^(3*10^12). The only additional assumption is Platt's modulus-one finite RH
through height 100,000,000, declared in PlattAssumption. -/
theorem chen {N : ℕ} (hN : chenCutoff ≤ N) (hEven : Even N) :
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q :=
  H29.chen_of_lower (square_cutoff_le.trans hN) hEven (weighted_lower hN hEven)

/-- Literal recovery of the original repository's implicit existence statement. -/
theorem original_chen : Goldbach.ChenTheorem :=
  ⟨chenCutoff, fun _ hN he => chen hN he⟩

#print axioms weighted_lower
#print axioms chen
#print axioms original_chen
end ChenEffective.H29Core

end
end
