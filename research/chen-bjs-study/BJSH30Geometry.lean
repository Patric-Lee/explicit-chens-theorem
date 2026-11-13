import BJSH30DistributionGeometry
import BJSTightGeometry

noncomputable section
namespace ChenEffective.H30
open Real Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem small_prime_product_log (S : BoundingSieve) (U : ℝ) (hU : 0≤U) :
    log (smallSievePrimeProduct S U:ℝ)≤2*U := by
  have hh := presieve_log_cost (S.prodPrimes.primeFactors.filter (fun p : ℕ => (p:ℝ)<U)) hU
    (fun p hp => ⟨Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1,(mem_filter.mp hp).2.le⟩)
  have hl4 : log (4:ℝ)≤2 := by
    rw [show (4:ℝ)=2^2 by norm_num,log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [log_two_lt_d9]
  have hc : (smallSievePrimeProduct S U:ℝ)=
      ∏ p∈S.prodPrimes.primeFactors.filter (fun p : ℕ => (p:ℝ)<U),(p:ℝ) := by
    simp only [smallSievePrimeProduct,Nat.cast_prod]
  rw [hc]
  exact hh.trans (mul_le_mul_of_nonneg_right hl4 hU)

noncomputable def ratio (S : BoundingSieve) (U X z : ℝ) : ℝ :=
  log (X/(2*(smallSievePrimeProduct S U:ℝ)))/log z

theorem ratio_shift (S : BoundingSieve) {N : ℕ} (hn : 0<N) {U X : ℝ}
    (hU : 0≤U) (hX : 0<X) (hBudget : (10^6:ℝ)*(1+2*U)≤log (N:ℝ)) :
    0≤log X/log ((N:ℝ)^(1/10:ℝ))-ratio S U X ((N:ℝ)^(1/10:ℝ)) ∧
    log X/log ((N:ℝ)^(1/10:ℝ))-ratio S U X ((N:ℝ)^(1/10:ℝ))≤1/10^5 := by
  let Q := smallSievePrimeProduct S U
  have hQnat : 0<Q := Nat.pos_of_ne_zero
    (S.prodPrimes_squarefree.squarefree_of_dvd (smallSievePrimeProduct_dvd S U)).ne_zero
  have hQ : (0:ℝ)<Q := by exact_mod_cast hQnat
  have hQ1 : (1:ℝ)≤Q := by exact_mod_cast hQnat
  have hnR : (0:ℝ)<N := by exact_mod_cast hn
  have hL : 0<log (N:ℝ) := by nlinarith only [hBudget,hU]
  have hq0 : 0≤log (2*(Q:ℝ)) := log_nonneg (by linarith only [hQ1])
  have hqcap : log (2*(Q:ℝ))≤1+2*U := by
    rw [log_mul (by norm_num) hQ.ne']
    have hh := small_prime_product_log S U hU
    change log (Q:ℝ)≤_ at hh
    linarith only [hh,log_two_lt_d9]
  unfold ratio
  rw [log_div hX.ne' (mul_pos (by norm_num) hQ).ne',log_rpow hnR]
  constructor
  · have hh := div_nonneg hq0 (show 0≤(1/10:ℝ)*log (N:ℝ) by positivity)
    convert hh using 1 <;> first | rfl | ring
  · have hh : log (2*(Q:ℝ))/((1/10:ℝ)*log (N:ℝ))≤1/10^5 := by
      apply (div_le_iff₀ (by positivity : 0<(1/10:ℝ)*log (N:ℝ))).mpr
      nlinarith only [hqcap,hBudget,hU]
    convert hh using 1
    ring

theorem ratio_shift_near_H30 (S : BoundingSieve) {N : ℕ} (hN : distributionThreshold≤N)
    {U X : ℝ} (hU : 0≤U) (hUcap : U≤4000000) (hX : 0<X) :
    0≤log X/log ((N:ℝ)^(1/10:ℝ))-ratio S U X ((N:ℝ)^(1/10:ℝ)) ∧
    log X/log ((N:ℝ)^(1/10:ℝ))-ratio S U X ((N:ℝ)^(1/10:ℝ))≤1/10^5 := by
  have hL := distribution_log hN
  have hn9 := (numerical_prime_pair_parameters (show (10^12:ℝ)≤log (N:ℝ) by linarith only [hL])).1
  exact ratio_shift S (by omega) hU hX (by nlinarith only [hL,hUcap])

#print axioms ratio_shift_near_H30
end ChenEffective.H30
