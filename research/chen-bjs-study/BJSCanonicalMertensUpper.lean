import BJSStudyElementaryMertens
import AnalyticNumberTheory.Mertens.FinitePart

/-! A certified numerical upper bound for the CANONICAL Mertens constant.
Only standard axioms: a finite harmonic sum bounds gamma, and eight actual
prime Euler corrections, bounded by positive Taylor sums, bound its tail.
-/
noncomputable section
namespace ChenEffective
open Real Finset AnalyticNumberTheory.Mertens
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0

theorem bjsStudy_gamma_upper : eulerMascheroniConstant ≤ (29/50 : ℝ) := by
  have hH : (harmonic 256 : ℝ)≤(49/8 : ℝ) := by norm_num [harmonic,Finset.sum_range_succ]
  have hg := eulerMascheroniConstant_lt_eulerMascheroniSeq' 256
  norm_num only [eulerMascheroniSeq',show (256 : ℕ)≠0 by decide,if_false] at hg
  have hl : log (256 : ℝ)=8*log 2 := by
    rw [show (256 : ℝ)=2^(8 : ℕ) by norm_num,log_pow]
    norm_num
  rw [hl] at hg
  linarith only [hg,hH,log_two_gt_d9]

theorem bjsStudy_euler_correction_nonneg (p : ℕ) : 0 ≤ logarithmicCorrectionTerm p := by
  unfold logarithmicCorrectionTerm
  split_ifs with hp
  · have hh := log_le_sub_one_of_pos (primeFactor_pos hp)
    linarith only [hh]
  · rfl

theorem bjsStudy_euler_correction_taylor (p : ℕ) (hp : p.Prime) :
    (∑ k∈range 16, (1/(p : ℝ))^(k+1)/(k+1))-1/(p : ℝ) ≤ logarithmicCorrectionTerm p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hx0 : 0≤1/(p : ℝ) := by positivity
  have hx1 : |1/(p : ℝ)|<1 := by
    rw [abs_of_nonneg hx0]
    exact (div_lt_one (by linarith only [hp1])).mpr hp1
  have hs := hasSum_pow_div_log_of_abs_lt_one hx1
  have hh := Summable.sum_le_tsum (range 16) (fun k _ => by positivity) hs.summable
  rw [hs.tsum_eq] at hh
  simp only [logarithmicCorrectionTerm,if_pos hp]
  linarith only [hh]

theorem bjsStudy_correction_limit_lower : (31/100 : ℝ) ≤ logarithmicCorrectionLimit := by
  let F : Finset ℕ := {2,3,5,7,11,13,17,19}
  have hprime : ∀ p∈F, p.Prime := by norm_num [F]
  have hfinite : (31/100 : ℝ)≤∑ p∈F, ((∑ k∈range 16, (1/(p : ℝ))^(k+1)/(k+1))-1/(p : ℝ)) := by
    norm_num [F,Finset.sum_range_succ]
  have hcompare := sum_le_sum (fun p hp => bjsStudy_euler_correction_taylor p (hprime p hp))
  have htail := Summable.sum_le_tsum F (fun p _ => bjsStudy_euler_correction_nonneg p)
    summable_logarithmicCorrectionTerm
  exact hfinite.trans (hcompare.trans htail)

theorem bjsStudy_canonical_mertens_upper : mertensSecondConstant≤(27/100 : ℝ) := by
  have hid := mertensConstant_eq_eulerMascheroni
  linarith only [hid,bjsStudy_gamma_upper,bjsStudy_correction_limit_lower]

#print axioms bjsStudy_canonical_mertens_upper
end ChenEffective
