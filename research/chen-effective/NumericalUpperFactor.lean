import NumericalLowerFactor
import MathlibNt.SieveTheory.LinearSieve.DimensionOneUpperFactor

noncomputable section
namespace ChenEffective
open Real Set MeasureTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem numerical_inner_increment {u v : ℝ} (hu : 3 ≤ u) (huv : u ≤ v) (hv : v ≤ 4) :
    0 ≤ jurkatRichertInnerIntegral v-jurkatRichertInnerIntegral u ∧
      jurkatRichertInnerIntegral v-jurkatRichertInnerIntegral u ≤ v-u := by
  have hint {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
      IntervalIntegrable (fun t : ℝ => Real.log (t-1)/t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    apply ContinuousOn.div
    · apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
      intro t ht
      change t-1 ≠ 0
      linarith only [ht.1,ha]
    · exact continuousOn_id
    · intro t ht
      linarith only [ht.1,ha]
  have hi := hint (a := u-1) (b := v-1) (by linarith) (by linarith) (by linarith)
  have hpoint (t : ℝ) (ht : t ∈ Icc (u-1) (v-1)) : 0 ≤ Real.log (t-1)/t ∧ Real.log (t-1)/t ≤ 1 := by
    have ht0 : 0 < t := by linarith only [ht.1,hu]
    have hl := Real.log_le_sub_one_of_pos (show 0 < t-1 by linarith only [ht.1,hu])
    exact ⟨div_nonneg (Real.log_nonneg (by linarith only [ht.1,hu])) ht0.le,
      (div_le_one ht0).mpr (by linarith only [hl])⟩
  have hp := intervalIntegral.integral_nonneg (μ := volume) (show u-1 ≤ v-1 by linarith) (fun t ht => (hpoint t ht).1)
  have hb : (∫ t in u-1..v-1, Real.log (t-1)/t) ≤ v-u := by
    calc
      _ ≤ ∫ _t in u-1..v-1, (1 : ℝ) := intervalIntegral.integral_mono_on (by linarith) hi intervalIntegrable_const (fun t ht => (hpoint t ht).2)
      _ = _ := by simp
  have ha := intervalIntegral.integral_add_adjacent_intervals
    (hint (a := 2) (b := u-1) (by norm_num) (by linarith) (by linarith)) hi
  unfold jurkatRichertInnerIntegral
  constructor <;> linarith only [ha,hp,hb]

def upperFactorAux (s : ℝ) : ℝ := jurkatRichertInnerIntegral (max 3 s)
theorem upperFactorAux_bounds {s : ℝ} (hs : s ≤ 4) : 0 ≤ upperFactorAux s ∧ upperFactorAux s ≤ 1 :=
  numerical_inner_integral (le_max_left _ _) (max_le (by norm_num) hs)

theorem upperFactorAux_lipschitz {s t : ℝ} (hs : s ≤ 4) (ht : t ≤ 4) :
    |upperFactorAux s-upperFactorAux t| ≤ |s-t| := by
  have hmax : |max 3 s-max 3 t| ≤ |s-t| := by
    simpa only [max_comm] using abs_max_sub_max_le_abs s t (3 : ℝ)
  have hh : |upperFactorAux s-upperFactorAux t| ≤ |max 3 s-max 3 t| := by
    unfold upperFactorAux
    rcases le_total (max (3 : ℝ) s) (max 3 t) with h | h
    · obtain ⟨h0,h1⟩ := numerical_inner_increment (le_max_left _ _) h (max_le (by norm_num) ht)
      rw [abs_sub_comm,abs_of_nonneg h0,abs_sub_comm (max 3 s),abs_of_nonneg (sub_nonneg.mpr h)]
      exact h1
    · obtain ⟨h0,h1⟩ := numerical_inner_increment (le_max_left _ _) h (max_le (by norm_num) hs)
      rw [abs_of_nonneg h0,abs_of_nonneg (sub_nonneg.mpr h)]
      exact h1
  exact hh.trans hmax

theorem numerical_upper_factor_formula (s : ℝ) : jurkatRichertUpperLinearSieveFactor s =
    (2*Real.exp Real.eulerMascheroniConstant)/s*(1+upperFactorAux s) := by
  unfold jurkatRichertUpperLinearSieveFactor upperFactorAux
  split_ifs with h
  · rw [max_eq_left h]
    norm_num [jurkatRichertInnerIntegral]
  · rw [max_eq_right (le_of_not_ge h)]

theorem numerical_upper_factor_regular {s t : ℝ} (hs : s ∈ Icc (1 : ℝ) 4) (ht : t ∈ Icc (1 : ℝ) 4) :
    0 ≤ jurkatRichertUpperLinearSieveFactor s ∧ jurkatRichertUpperLinearSieveFactor s ≤ 12 ∧
      |jurkatRichertUpperLinearSieveFactor s-jurkatRichertUpperLinearSieveFactor t| ≤ 18*|s-t| := by
  let C := 2*Real.exp Real.eulerMascheroniConstant
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hC6 : C ≤ 6 := by
    have he := (Real.exp_le_exp.mpr (Real.eulerMascheroniConstant_lt_two_thirds.le.trans (by norm_num))).trans (Real.exp_one_lt_d9.le.trans (by norm_num : (2.7182818286 : ℝ) ≤ 3))
    dsimp [C]
    linarith only [he]
  have hs0 : 0 < s := zero_lt_one.trans_le hs.1
  have ht0 : 0 < t := zero_lt_one.trans_le ht.1
  obtain ⟨ha0,ha1⟩ := upperFactorAux_bounds hs.2
  obtain ⟨hb0,hb1⟩ := upperFactorAux_bounds ht.2
  have hCs : 0 ≤ C/s := div_nonneg hC0 hs0.le
  have hCs6 : C/s ≤ 6 := (div_le_self hC0 hs.1).trans hC6
  have hCt12 : |C*(1+upperFactorAux t)| ≤ 12 := by
    rw [abs_of_nonneg (by positivity)]
    have hh := mul_le_mul hC6 (show 1+upperFactorAux t ≤ 2 by linarith) (by positivity) (by norm_num : (0 : ℝ) ≤ 6)
    linarith only [hh]
  have hrec : |1/s-1/t| ≤ |s-t| := by
    rw [show (1/s-1/t)=(t-s)/(s*t) by field_simp,abs_div,abs_of_pos (mul_pos hs0 ht0),abs_sub_comm]
    exact div_le_self (abs_nonneg _) (by nlinarith only [hs.1,ht.1,mul_nonneg (sub_nonneg.mpr hs.1) (sub_nonneg.mpr ht.1)])
  have hdiff := upperFactorAux_lipschitz hs.2 ht.2
  have hfirst : |C/s*(upperFactorAux s-upperFactorAux t)| ≤ 6*|s-t| := by
    rw [abs_mul,abs_of_nonneg hCs]
    exact mul_le_mul hCs6 hdiff (abs_nonneg _) (by norm_num)
  have hsecond : |C*(1+upperFactorAux t)*(1/s-1/t)| ≤ 12*|s-t| := by
    rw [abs_mul]
    exact mul_le_mul hCt12 hrec (abs_nonneg _) (by norm_num)
  rw [numerical_upper_factor_formula,numerical_upper_factor_formula]
  change 0 ≤ C/s*(1+upperFactorAux s) ∧ _
  refine ⟨by positivity,?_,?_⟩
  · have hh := mul_le_mul hCs6 (show 1+upperFactorAux s ≤ 2 by linarith) (by positivity) (by norm_num : (0 : ℝ) ≤ 6)
    linarith only [hh]
  · rw [show C/s*(1+upperFactorAux s)-C/t*(1+upperFactorAux t) =
      C/s*(upperFactorAux s-upperFactorAux t)+C*(1+upperFactorAux t)*(1/s-1/t) by ring]
    exact (abs_add_le _ _).trans (by linarith only [hfirst,hsecond])

def mediumPrimeProfile (a : ℝ) : ℝ := jurkatRichertUpperLinearSieveFactor (5-10*a)
theorem numerical_medium_profile {a b : ℝ} (ha : a ∈ Icc (1/10 : ℝ) (1/3)) (hb : b ∈ Icc (1/10 : ℝ) (1/3)) :
    0 ≤ mediumPrimeProfile a ∧ mediumPrimeProfile a ≤ 12 ∧
      |mediumPrimeProfile a-mediumPrimeProfile b| ≤ 180*|a-b| := by
  obtain ⟨h0,h1,h2⟩ := numerical_upper_factor_regular
    (show 5-10*a ∈ Icc (1 : ℝ) 4 by constructor <;> linarith only [ha.1,ha.2])
    (show 5-10*b ∈ Icc (1 : ℝ) 4 by constructor <;> linarith only [hb.1,hb.2])
  refine ⟨h0,h1,?_⟩
  have heq : |(5-10*a)-(5-10*b)| = 10*|a-b| := by
    rw [show (5-10*a)-(5-10*b)= -(10*(a-b)) by ring,abs_neg,abs_mul]
    norm_num
  rw [heq] at h2
  dsimp only [mediumPrimeProfile]
  linarith only [h2]

#print axioms numerical_medium_profile
end ChenEffective
