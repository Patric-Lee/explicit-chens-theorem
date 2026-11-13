import BJSH30WeightedDistribution
import NumericalVaryingCorrections
import NumericalUpperDistribution
import NumericalSquareThresholdCap

noncomputable section
namespace ChenEffective.H30
open Real Finset
open MathlibNt.SieveTheory SwitchingPrinciple LiuWeight
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem distribution_log_cutoff {k : ℕ} (hk : 16*(k+1)^2≤10^13) :
    logPowerCutoff k≤ distributionThreshold := by
  unfold distributionThreshold
  apply numerical_log_cutoff_cap
  rw [distributionExponent_eq]
  exact hk

theorem distribution_parameters {N : ℕ} (hN : distributionThreshold≤ N) :
    9≤ N ∧ 0< log (N:ℝ) ∧ logPowerCutoff 100≤ N := by
  have hcut := (distribution_log_cutoff (by norm_num : 16*((100:ℕ)+1)^2≤10^13)).trans hN
  have hn9 := (logPowerCutoff_nine_le _).trans hcut
  exact ⟨hn9,log_pos (by exact_mod_cast (show 1< N by omega)),hcut⟩

theorem base_bv_order_three {N : ℕ} (hN : distributionThreshold≤ N) :
    (∑ q∈Icc 1 (panModulusCutoff N (highBVExponent 10:ℝ)),
      BombieriVinogradov.standardPrimeAPPrefixMaxError N q)≤(N:ℝ)/log (N:ℝ)^3 := by
  have hL := distribution_log hN
  have hl := (distribution_parameters hN).2.1
  have hb := numerical_BV 10 N ((distribution_bv_cap (by decide : 10≤30)).trans hN)
  have hc : numericalBVConstant 10≤ log (N:ℝ)^7 := by
    have hh : numericalBVConstant 10≤(2*10^18:ℝ) := by
      norm_num [numericalBVConstant,bvConstant,primitiveNumericalConstant,principalNumericalConstant,highBVConductorExponent]
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤10^13) hL 7
    nlinarith only [hh,hp]
  apply hb.trans
  calc
    _ ≤ log (N:ℝ)^7*N/log (N:ℝ)^10 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg N)) (pow_nonneg hl.le _)
    _ = _ := by field_simp

theorem weighted_distribution_paid (m N : ℕ) (hm : 0 < m)
    (hN : distributionThreshold≤ N) (hBudget : m*highBVExponent (weightedSaving 6)≤3*10^11) :
    jurkatRichertSourceReducedWeightedBVSum N (1/(m:ℝ))≤
      (1/10^8:ℝ)*(N:ℝ)/log (N:ℝ)^2 := by
  have hL := distribution_log hN
  have hl := (distribution_parameters hN).2.1
  have hb := weighted_distribution_of_log 6 m N hm hL
    ((distribution_bv_cap (by norm_num [weightedSaving] : weightedSaving 6≤30)).trans hN) hBudget
  have hc : weightedNumericalConstant 6≤(1/10^8:ℝ)*log (N:ℝ)^4 := by
    have hh : weightedNumericalConstant 6≤(10^26:ℝ) := by
      norm_num [weightedNumericalConstant,weightedSaving,numericalBVConstant,bvConstant,
        primitiveNumericalConstant,principalNumericalConstant,highBVConductorExponent]
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤10^13) hL 4
    nlinarith only [hh,hp]
  apply hb.trans
  calc
    _ ≤ ((1/10^8:ℝ)*log (N:ℝ)^4)*N/log (N:ℝ)^6 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg N)) (pow_nonneg hl.le _)
    _ = _ := by field_simp

theorem varying_distribution_paid (m d N : ℕ) (hm : 0 < m) (hd : 0< d) (hdcap : d≤10^7)
    (hN : distributionThreshold≤ N) (hBudget : m*highBVExponent (weightedSaving 6)≤3*10^11)
    (hEven : Even N) :
    jurkatRichertSourceVaryingQRemainderSum N (1/(m:ℝ))≤
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
  have hf := jurkatRichertSourceVaryingQRemainderSum_le_weightedBV_add_correction N (1/(m:ℝ)) hEven (by omega)
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

#print axioms varying_distribution_paid
end ChenEffective.H30
