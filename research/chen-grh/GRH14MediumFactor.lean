import GRH14MediumKernelCertificates
import NumericalUpperFactor

noncomputable section
namespace ChenEffective.GRH14
open Real Set
open MathlibNt.SieveTheory.SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem upper_aux_mono {s t : ℝ} (hst : s ≤ t) (ht : t ≤ 4) :
    upperFactorAux s ≤ upperFactorAux t := by
  have hmax : max (3:ℝ) s ≤ max 3 t := max_le_max_left _ hst
  exact (sub_nonneg.mp (numerical_inner_increment (le_max_left _ _) hmax (max_le (by norm_num) ht)).1)

theorem upper_factor_shift {s t : ℝ} (hs : (3/2:ℝ) ≤ s) (hst : s ≤ t) (ht : t ≤ 4) :
    jurkatRichertMertensFactor*
      (jurkatRichertUpperLinearSieveFactor s-jurkatRichertUpperLinearSieveFactor t) ≤ 50*(t-s)/(s*t) := by
  have hs0 : 0<s := by linarith only [hs]
  have ht0 : 0<t := hs0.trans_le hst
  have haux := upper_aux_mono hst ht
  have hquarter := (inner_integral_quarter (le_max_left (3:ℝ) t) (max_le (by norm_num) ht)).2
  change upperFactorAux t ≤ 1/4 at hquarter
  have haux0 := (upperFactorAux_bounds ht).1
  have hB0 : 0 ≤ jurkatRichertMertensFactor := by unfold jurkatRichertMertensFactor; positivity
  have hA0 : 0 ≤ 2*exp eulerMascheroniConstant := by positivity
  have hab : jurkatRichertMertensFactor*(2*exp eulerMascheroniConstant)=40 := by
    unfold jurkatRichertMertensFactor
    have hh : exp (-eulerMascheroniConstant)*exp eulerMascheroniConstant=1 := by
      rw [← exp_add,neg_add_cancel,exp_zero]
    nlinarith only [hh]
  have hmain : jurkatRichertUpperLinearSieveFactor s-jurkatRichertUpperLinearSieveFactor t ≤ (2*exp eulerMascheroniConstant)*(1+upperFactorAux t)*(t-s)/(s*t) := by
    rw [numerical_upper_factor_formula,numerical_upper_factor_formula]
    have hh := mul_le_mul_of_nonneg_left haux (div_nonneg hA0 hs0.le)
    have heq : (2*exp eulerMascheroniConstant)/s*(1+upperFactorAux t)-
        (2*exp eulerMascheroniConstant)/t*(1+upperFactorAux t) =
        (2*exp eulerMascheroniConstant)*(1+upperFactorAux t)*(t-s)/(s*t) := by
      field_simp
    linarith only [hh,heq]
  calc
    _ ≤ jurkatRichertMertensFactor*
        ((2*exp eulerMascheroniConstant)*(1+upperFactorAux t)*(t-s)/(s*t)) :=
      mul_le_mul_of_nonneg_left hmain hB0
    _ = (jurkatRichertMertensFactor*(2*exp eulerMascheroniConstant))*
        ((1+upperFactorAux t)*(t-s)/(s*t)) := by ring
    _ = 40*(1+upperFactorAux t)*(t-s)/(s*t) := by rw [hab]; ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (mul_nonneg hs0.le ht0.le)
      nlinarith only [mul_nonneg (show 0 ≤ t-s by linarith only [hst])
        (show 0 ≤ 1/4-upperFactorAux t by linarith only [hquarter])]

theorem upper_factor_window {s t : ℝ} (hs : (3/2:ℝ) ≤ s) (hst : s ≤ t) (ht : t ≤ 4)
    (hshift : t-s ≤ 71/1000) :
    jurkatRichertMertensFactor*
      (jurkatRichertUpperLinearSieveFactor s-jurkatRichertUpperLinearSieveFactor t) ≤ (71/20:ℝ)/(t-71/1000)^2 := by
  have hs0 : 0<s := by linarith only [hs]
  have ht0 : 0<t := hs0.trans_le hst
  have hden0 : 0<t-71/1000 := by linarith only [hs,hst]
  have hden : (t-71/1000)^2 ≤ s*t := by
    have ha : 0 ≤ s-(t-71/1000) := by linarith only [hshift]
    have hb : 0 ≤ t-(t-71/1000) := by norm_num
    nlinarith only [mul_nonneg ha ht0.le,mul_nonneg hb hden0.le]
  apply (upper_factor_shift hs hst ht).trans
  apply (div_le_div_iff₀ (mul_pos hs0 ht0) (sq_pos_of_pos hden0)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hshift (sq_nonneg (t-71/1000)),hden]

theorem medium_exp_polynomial_bounds {u : ℝ} (hu : 0 ≤ u) :
    1 ≤ mediumExpPolynomial u ∧ mediumExpPolynomial u ≤ exp u := by
  constructor
  · unfold mediumExpPolynomial
    have hh : 0 ≤ u+u^2/2+u^3/6+u^4/24+u^5/120+u^6/720 := by positivity
    linarith only [hh]
  · have hh := sum_le_exp_of_nonneg hu 7
    norm_num [Finset.sum_range_succ] at hh
    convert hh using 1 <;> unfold mediumExpPolynomial <;> ring

theorem medium_hat_envelope_bound {s : ℝ} (hs : (3/2:ℝ) ≤ s) :
    exp 2*sieveHat s ≤ mediumHatEnvelope s := by
  have hs0 : 0<s := by linarith only [hs]
  unfold mediumHatEnvelope
  by_cases hs2 : s ≤ 2
  · rw [if_pos hs2]
    unfold sieveHat
    rw [if_pos hs2,← exp_add]
    norm_num
  · rw [if_neg hs2]
    have hu : 0 ≤ s-2 := by linarith only [hs2]
    have hp := medium_exp_polynomial_bounds hu
    have hrec : 1/exp (s-2) ≤ 1/mediumExpPolynomial (s-2) :=
      one_div_le_one_div_of_le (by linarith only [hp.1]) hp.2
    have heq : exp 2*exp (-s)=1/exp (s-2) := by
      rw [← exp_add,one_div,← exp_neg]
      congr 1
      ring
    by_cases hs3 : s ≤ 3
    · rw [if_pos hs3]
      unfold sieveHat
      rw [if_neg hs2,if_pos hs3,heq]
      exact hrec
    · rw [if_neg hs3]
      unfold sieveHat
      rw [if_neg hs2,if_neg hs3]
      have hh := mul_le_mul_of_nonneg_left hrec
        (show 0 ≤ (3:ℝ)/s by positivity)
      calc
        _ = (3/s)*(exp 2*exp (-s)) := by ring
        _ = (3/s)*(1/exp (s-2)) := by rw [heq]
        _ ≤ (3/s)*(1/mediumExpPolynomial (s-2)) := hh
        _ = _ := by ring

#print axioms upper_factor_window
#print axioms medium_hat_envelope_bound
end ChenEffective.GRH14
