/- Threshold-specialized companion of research/chen-effective/NumericalPanNormalization.lean.
The original producer is retained; all modified numerical statements are rechecked. -/
import BJSH30PanSource
import NumericalMertensProduct

noncomputable section
namespace ChenEffective.H30
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiuWeight
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def panDivisorConstant : ℝ := (2*Real.exp Real.eulerMascheroniConstant)^3

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
    (by unfold panDivisorConstant; ring))

def panNormalizationConstant : ℝ := 3*panDivisorConstant*|2-2/Real.log 2|
def panCanonicalConstant (A : ℕ) : ℝ := panWeightedConstant A+panNormalizationConstant
@[irreducible] def panCanonicalThreshold (A m : ℕ) : ℕ :=
  max (panSourceThreshold A m) (max (mertensProductThreshold 2) (logPowerCutoff (3*(A+3))))

theorem numerical_pan_canonical (A m N : ℕ) (hm : 0 < m)
    (hN : panCanonicalThreshold A m ≤ N) :
    LiuPaperQCoprimeRBound (liuLogarithmicIntegral 2) N (1/(m : ℝ))
      (A : ℝ) (panCanonicalConstant A) := by
  have hn := hN
  unfold panCanonicalThreshold at hn
  obtain ⟨hNS, hNM, hNP⟩ := (max_le_iff.mp hn).imp_right max_le_iff.mp
  have hN9 := (logPowerCutoff_nine_le _).trans hNP
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hε : 0 ≤ 1/(m : ℝ) := by positivity
  have hmass := sum_liuWeight_Icc_le_three_mul_rpow_two_thirds N
    (liuSourceZ10 N) (liuSourceY3 N) (by omega)
  have hcut := (paperQSourceCutoff_le_floor_cuberoot N (1/(m : ℝ)) (by omega) hε).trans
    (liuSourceY3_le N (by omega))
  have hdiv := numerical_pan_full_divisor hNM hcut
  have hmass0 : 0 ≤ ∑ a ∈ Icc 1 N, liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a := by
    apply sum_nonneg
    intro a _
    exact liuWeight_nonneg _ _ _ _
  have hfactor : 0 ≤ paperQStyleFullDivisorWeightSum N (paperQSourceCutoff N (1/(m : ℝ))) := by
    unfold paperQStyleFullDivisorWeightSum
    positivity
  have hnorm := liuPaperQSourceCoprimeDistributionMajorant_li_normalization_le
    2 (2/Real.log 2) N (1/(m : ℝ))
  have hloss : |2-2/Real.log 2| *
      (∑ a ∈ Icc 1 N, liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a)*
      paperQStyleFullDivisorWeightSum N (paperQSourceCutoff N (1/(m : ℝ))) ≤
        panNormalizationConstant*N/Real.log (N : ℝ)^A := by
    have hp := log_pow_le_rpow_inv_explicit (k := A+3) (m := 3)
      (by norm_num) (le_refl _) hNP
    norm_num only [Nat.cast_ofNat] at hp
    have hscale : (N : ℝ)^(2/3 : ℝ)*Real.log (N : ℝ)^3 ≤ N/Real.log (N : ℝ)^A := by
      apply (le_div_iff₀ (pow_pos hlog A)).mpr
      calc
        _ = (N : ℝ)^(2/3 : ℝ)*Real.log (N : ℝ)^(A+3) := by rw [pow_add]; ring
        _ ≤ (N : ℝ)^(2/3 : ℝ)*(N : ℝ)^(1/3 : ℝ) := by gcongr
        _ = _ := by rw [← Real.rpow_add hN0]; norm_num
    calc
      _ ≤ |2-2/Real.log 2| *(3*(N : ℝ)^(2/3 : ℝ))*(panDivisorConstant*Real.log (N : ℝ)^3) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hmass (abs_nonneg _)) hdiv hfactor
          (by positivity)
      _ = panNormalizationConstant*((N : ℝ)^(2/3 : ℝ)*Real.log (N : ℝ)^3) := by
        unfold panNormalizationConstant; ring
      _ ≤ panNormalizationConstant*(N/Real.log (N : ℝ)^A) := by
        apply mul_le_mul_of_nonneg_left hscale
        unfold panNormalizationConstant panDivisorConstant
        positivity
      _ = _ := by ring
  unfold LiuPaperQCoprimeRBound
  rw [Real.rpow_natCast]
  have hsource := numerical_pan_source A m N hm hNS
  unfold LiuPaperQCoprimeRBound at hsource
  rw [Real.rpow_natCast] at hsource
  exact hnorm.trans ((add_le_add hsource hloss).trans_eq (by unfold panCanonicalConstant; ring))

#print axioms numerical_pan_canonical
end ChenEffective.H30
