import GRH14PanWeighted
import GRH14MertensProduct
import BJSH30PanNormalization

noncomputable section
namespace ChenEffective.GRH14
open Real Finset
open MathlibNt.SieveTheory LiuWeight
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem pan_log_power_at_target {N : ℕ} (hN : targetCutoff≤N) {k : ℕ}
    (hk : k≤100) {δ : ℝ} (hδ : (1/600:ℝ)≤δ) :
    log (N:ℝ)^k≤(N:ℝ)^δ := by
  have hL := target_log_lower hN
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hn : 0<N := by
    by_contra h
    have hh : N=0 := by omega
    subst N
    norm_num at hL
  have hnR : (0:ℝ)<N := by exact_mod_cast hn
  have hkR : (k:ℝ)≤100 := by exact_mod_cast hk
  have hh := mul_le_mul_of_nonneg_left (pan_log_log_cap hL) (Nat.cast_nonneg k)
  have hm := mul_le_mul_of_nonneg_right hkR (show 0≤log (N:ℝ)/60000 by positivity)
  have hd := mul_le_mul_of_nonneg_right hδ hl.le
  rw [Real.rpow_def_of_pos hnR]
  calc
    _ = exp ((k:ℝ)*log (log (N:ℝ))) := by rw [exp_nat_mul (log (log (N:ℝ))) k,exp_log hl]
    _ ≤ _ := exp_le_exp.mpr (by nlinarith only [hh,hm,hd])

theorem pan_source_support_at_target {N : ℕ} (hN : targetCutoff≤N) :
    liuPanSourceIntervalLower N (38:ℝ)<liuSourceZ10 N := by
  have hN9 := (logPowerCutoff_nine_le 0).trans (pan_log_cutoff_at_target (k:=0) (by norm_num) hN)
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hp := pan_log_power_at_target hN (k:=76) (by norm_num) (δ:=(1/20:ℝ)) (by norm_num)
  have hlarge : 2^20≤N := by
    have hh := pan_log_cutoff_at_target (k:=1) (by norm_num) hN
    have hc : 2^20≤logPowerCutoff 1 := by norm_num [logPowerCutoff]
    exact hc.trans hh
  have htwo : (2:ℝ)≤(N:ℝ)^(1/20:ℝ) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num : (0:ℝ)≤2) hn.le (by norm_num : (0:ℝ)<20)).mpr
    norm_num
    exact_mod_cast hlarge
  have hs : ((N:ℝ)^(1/20:ℝ))^2=(N:ℝ)^(1/10:ℝ) := by
    rw [← rpow_natCast,← rpow_mul hn.le]
    norm_num
  have hb : log (N:ℝ)^76+2≤(N:ℝ)^(1/10:ℝ) := by nlinarith only [hp,htwo,hs]
  have hh := Nat.floor_mono hb
  have hL := target_log_lower hN
  have hl : 0≤log (N:ℝ) := by linarith only [hL]
  have hadd : ⌊log (N:ℝ)^76+2⌋₊=⌊log (N:ℝ)^76⌋₊+2 := by
    convert Nat.floor_add_natCast (pow_nonneg hl 76) 2 using 1 <;> norm_num
  rw [hadd] at hh
  unfold liuPanSourceIntervalLower liuSourceZ10
  norm_num only [rpow_ofNat]
  omega

theorem pan_source_level_at_target {N : ℕ} (hN : targetCutoff≤N) :
    liuSourceDEpsilon N (1/500:ℝ)≤panModulusCutoff N (39:ℝ) := by
  have hN9 := (logPowerCutoff_nine_le 0).trans (pan_log_cutoff_at_target (k:=0) (by norm_num) hN)
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hL := target_log_lower hN
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hp := pan_log_power_at_target hN (k:=39) (by norm_num) (δ:=(1/500:ℝ)) (by norm_num)
  unfold liuSourceDEpsilon panModulusCutoff
  apply Nat.floor_mono
  rw [rpow_sub hn]
  norm_num only [rpow_ofNat]
  exact div_le_div_of_nonneg_left (rpow_nonneg hn.le _) (pow_pos hl 39) hp

theorem pan_source_at_target {N : ℕ} (hN : targetCutoff≤N) :
    LiuPaperQCoprimeRBound (liuLogarithmicIntegral (2/log 2)) N (1/500:ℝ)
      (5:ℝ) (panWeightedConstant 5) := by
  have hN9 := (logPowerCutoff_nine_le 0).trans (pan_log_cutoff_at_target (k:=0) (by norm_num) hN)
  have hL := target_log_lower hN
  have hlog : 1<log (N:ℝ) := by linarith only [hL]
  have hb := numerical_pan_weighted 5 N hN (by norm_num)
  have hc := pan_source_level_at_target hN
  apply liuPaperQCoprimeRBound_of_liuMainPanEndpointMeanValueAt
    (liuLogarithmicIntegral (2/log 2)) N (1/500:ℝ) (5:ℝ) (39:ℝ)
    (panWeightedConstant 5) hc
  have hh := H30.liuMainPanEndpointWeightedSum_le_corollary230Sum (2/log 2) N
    (38:ℝ) (fun _ _ => liuMainPanCoprimeSum_eq_panSourceInterval _ (by omega)
      (pan_source_support_at_target hN))
    (range_panModulusCutoff_add_one_subset_sourceStrict N (38:ℝ) (by omega) hlog)
  norm_num only [panWeightedCutoff,panWeightedSaving,Nat.reduceMul,Nat.reduceAdd,Nat.cast_ofNat] at hb
  unfold LiuMainPanEndpointMeanValueAt
  convert hh.trans hb using 1 <;> norm_num only [rpow_ofNat]

#print axioms pan_source_at_target
end ChenEffective.GRH14


