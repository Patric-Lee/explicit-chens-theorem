/- Threshold-specialized companion to research/chen-bjs-study/BJSStudyGeometry.lean.
The original producer is retained. This companion rechecks its proof with
tighter numerical caps in the namespace ChenEffective.TightBudget. -/
import NumericalPreSieveDistribution
import BJSStudyProducts

noncomputable section
namespace ChenEffective.TightBudget
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

private opaque bjsStudyGeometryCertificate : {n : ℕ // n=3^(3^134)} := ⟨3^(3^134), rfl⟩
def bjsStudyGeometryThreshold : ℕ := bjsStudyGeometryCertificate.1
theorem bjsStudyGeometryThreshold_eq : bjsStudyGeometryThreshold=3^(3^134) :=
  bjsStudyGeometryCertificate.2

theorem bjsStudy_log_budget {N : ℕ} (hN : bjsStudyGeometryThreshold ≤ N) :
    10^6*(1+2*bjsStudyPresieveStart) ≤ log (N : ℝ) := by
  have hn := hN
  rw [bjsStudyGeometryThreshold_eq] at hn
  have hlog := log_ge_power_three hn
  have hU : (1 : ℝ) ≤ bjsStudyPresieveStart := by
    unfold bjsStudyPresieveStart
    exact one_le_pow₀ (by norm_num)
  have hcoef : (3*10^6 : ℝ) ≤ 3^14 := by norm_num
  have hexp : (3 : ℝ)^14 * bjsStudyPresieveStart ≤ (3 : ℝ)^134 := by
    unfold bjsStudyPresieveStart
    rw [← pow_add]
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hlog
  calc
    _ ≤ (3*10^6)*bjsStudyPresieveStart := by nlinarith only [hU]
    _ ≤ (3 : ℝ)^14*bjsStudyPresieveStart :=
      mul_le_mul_of_nonneg_right hcoef (zero_le_one.trans hU)
    _ ≤ (3 : ℝ)^134 := hexp
    _ ≤ _ := hlog

noncomputable def bjsStudyLevel (S : BoundingSieve) (X : ℝ) : ℕ :=
  ⌊X/(2*(smallSievePrimeProduct S bjsStudyPresieveStart : ℝ))⌋₊+1
noncomputable def bjsStudyRatio (S : BoundingSieve) (X z : ℝ) : ℝ :=
  log (X/(2*(smallSievePrimeProduct S bjsStudyPresieveStart : ℝ)))/log z

theorem bjsStudy_endpoint_parameters {N : ℕ} (hN : bjsStudyGeometryThreshold ≤ N) :
    2 ≤ N ∧ 2 ≤ (N : ℝ)^(1/10 : ℝ) := by
  have hh := bjsStudy_log_budget hN
  have hU : 0 < bjsStudyPresieveStart := by unfold bjsStudyPresieveStart; positivity
  have hL : 10^6 ≤ log (N : ℝ) := by nlinarith only [hh,hU]
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
    log X/log ((N : ℝ)^(1/10 : ℝ)) - bjsStudyRatio S X ((N : ℝ)^(1/10 : ℝ)) ≤ 1/10^5 := by
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
  · have hdiv : log (2*(Q : ℝ))/((1/10 : ℝ)*log (N : ℝ)) ≤ 1/10^5 := by
      apply (div_le_iff₀ (by positivity : 0 < (1/10 : ℝ)*log (N : ℝ))).mpr
      nlinarith only [hqcap, hlog, hU]
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
end ChenEffective.TightBudget
