import GRH14PanSource
import BJSH30PanNormalization

noncomputable section
namespace ChenEffective.GRH14
open Real Finset
open MathlibNt.SieveTheory LiuWeight
open AnalyticNumberTheory.LargeSieve
open NumericalPanHigh AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def panDivisorConstant : ℝ := H30.panDivisorConstant
def panNormalizationConstant : ℝ := H30.panNormalizationConstant
def panCanonicalConstant (A : ℕ) : ℝ := panWeightedConstant A+panNormalizationConstant
theorem numerical_pan_full_divisor {N w : ℕ} (hN : mertensProductThreshold 2 ≤ N)
    (hw : w ≤ N) :
    paperQStyleFullDivisorWeightSum N w ≤ panDivisorConstant*Real.log (N : ℝ)^3 := by
  have hprod := numerical_mertens_product (by norm_num : 0 < (2 : ℕ)) hN
  have hNP := (le_max_left _ _).trans hN
  have hN9 := (logPowerCutoff_nine_le _).trans hNP
  have hl0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hP := AnalyticNumberTheory.Mertens.primeProduct_pos N
  have hlow := (abs_le.mp hprod).1
  have hi : (AnalyticNumberTheory.Mertens.primeProduct N)⁻¹ ≤
      2*Real.exp Real.eulerMascheroniConstant*Real.log (N : ℝ) := by
    apply (inv_le_iff_one_le_mul₀ hP).mpr
    norm_num only [Nat.cast_ofNat] at hlow
    nlinarith only [hlow]
  have hh := paperQStyleFullDivisorWeightSum_le_primeProduct_inv_cube N w hw
  rw [MertensTheorem.primeProduct_eq_analyticNumberTheory] at hh
  exact hh.trans ((pow_le_pow_left₀ (by positivity) hi 3).trans_eq
    (by unfold panDivisorConstant H30.panDivisorConstant; ring))


theorem numerical_pan_canonical {N : ℕ} (hN : targetCutoff≤N) :
    LiuPaperQCoprimeRBound (liuLogarithmicIntegral 2) N (1/500:ℝ)
      (5:ℝ) (panCanonicalConstant 5) := by
  have hm : 0<(500:ℕ) := by norm_num

  have hNM : mertensProductThreshold 2≤N := by
    unfold mertensProductThreshold
    apply max_le (pan_log_cutoff_at_target (k:=2) (by norm_num) hN)
    exact (by
      unfold logPowerCutoff
      apply Nat.pow_le_pow_right (by norm_num)
      have hh := Nat.sqrt_le_self (6*2)
      omega : 3^(Nat.sqrt (6*2)+2)≤logPowerCutoff 0).trans
      (pan_log_cutoff_at_target (k:=0) (by norm_num) hN)
  have hNP : logPowerCutoff 24≤N := pan_log_cutoff_at_target (by norm_num) hN
  have hN9 := (logPowerCutoff_nine_le _).trans hNP
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hε : 0 ≤ 1/(500 : ℝ) := by positivity
  have hmass := sum_liuWeight_Icc_le_three_mul_rpow_two_thirds N
    (liuSourceZ10 N) (liuSourceY3 N) (by omega)
  have hcut := (paperQSourceCutoff_le_floor_cuberoot N (1/(500 : ℝ)) (by omega) hε).trans
    (liuSourceY3_le N (by omega))
  have hdiv := numerical_pan_full_divisor hNM hcut
  have hmass0 : 0 ≤ ∑ a ∈ Icc 1 N, liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a := by
    apply sum_nonneg
    intro a _
    exact liuWeight_nonneg _ _ _ _
  have hfactor : 0 ≤ paperQStyleFullDivisorWeightSum N (paperQSourceCutoff N (1/(500 : ℝ))) := by
    unfold paperQStyleFullDivisorWeightSum
    positivity
  have hnorm := liuPaperQSourceCoprimeDistributionMajorant_li_normalization_le
    2 (2/Real.log 2) N (1/(500 : ℝ))
  have hloss : |2-2/Real.log 2| *
      (∑ a ∈ Icc 1 N, liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a)*
      paperQStyleFullDivisorWeightSum N (paperQSourceCutoff N (1/(500 : ℝ))) ≤
        panNormalizationConstant*N/Real.log (N : ℝ)^5 := by
    have hp := log_pow_le_rpow_inv_explicit (k := 5+3) (m := 3)
      (by norm_num) (le_refl _) hNP
    norm_num only [Nat.cast_ofNat] at hp
    have hscale : (N : ℝ)^(2/3 : ℝ)*Real.log (N : ℝ)^3 ≤ N/Real.log (N : ℝ)^5 := by
      apply (le_div_iff₀ (pow_pos hlog 5)).mpr
      calc
        _ = (N : ℝ)^(2/3 : ℝ)*Real.log (N : ℝ)^(5+3) := by rw [pow_add]; ring
        _ ≤ (N : ℝ)^(2/3 : ℝ)*(N : ℝ)^(1/3 : ℝ) := by gcongr
        _ = _ := by rw [← Real.rpow_add hN0]; norm_num
    calc
      _ ≤ |2-2/Real.log 2| *(3*(N : ℝ)^(2/3 : ℝ))*(panDivisorConstant*Real.log (N : ℝ)^3) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hmass (abs_nonneg _)) hdiv hfactor
          (by positivity)
      _ = panNormalizationConstant*((N : ℝ)^(2/3 : ℝ)*Real.log (N : ℝ)^3) := by
        unfold panNormalizationConstant H30.panNormalizationConstant panDivisorConstant; ring
      _ ≤ panNormalizationConstant*(N/Real.log (N : ℝ)^5) := by
        apply mul_le_mul_of_nonneg_left hscale
        unfold panNormalizationConstant H30.panNormalizationConstant H30.panDivisorConstant
        positivity
      _ = _ := by ring
  unfold LiuPaperQCoprimeRBound
  norm_num only [Real.rpow_natCast,Real.rpow_ofNat]
  have hsource := pan_source_at_target hN
  unfold LiuPaperQCoprimeRBound at hsource
  norm_num only [Real.rpow_natCast,Real.rpow_ofNat] at hsource
  exact hnorm.trans ((add_le_add hsource hloss).trans_eq (by unfold panCanonicalConstant; ring))


#print axioms numerical_pan_canonical
end ChenEffective.GRH14



