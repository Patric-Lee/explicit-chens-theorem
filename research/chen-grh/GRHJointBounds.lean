import GRH125Analytic

/-! Bounds for joint cutoff optimization. The optimizer is not trusted;
each improvement below is proved from the existing analytic inputs. -/
noncomputable section
namespace ChenEffective.GRHJoint
open Real Set Finset MeasureTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory LiuWeight
set_option maxHeartbeats 4000000
set_option maxErrors 100
set_option backward.isDefEq.respectTransparency false

theorem inner_integrand_mono {x y : ℝ} (hx : 2≤ x) (hxy : x≤ y) (hy : y≤3) :
    log (x-1)/x ≤ log (y-1)/y := by
  have hx0 : 0<x := by linarith
  have hy0 : 0<y := by linarith
  have hx1 : 0<x-1 := by linarith
  have hy1 : 0<y-1 := by linarith
  have hr := log_le_sub_one_of_pos (div_pos hx1 hy1)
  rw [log_div hx1.ne' hy1.ne'] at hr
  have hd : (y-x)/(y-1) ≤ log (y-1)-log (x-1) := by
    have he : 1-(x-1)/(y-1)=(y-x)/(y-1) := by field_simp; ring
    linarith only [hr,he]
  have hm := (div_le_iff₀ hy1).mp hd
  have hl := log_le_sub_one_of_pos hx1
  have hlog0 : 0≤ log (x-1) := log_nonneg (by linarith)
  have hlog1 : log (x-1)≤1 := by linarith
  have hden : y-1≤ x := by linarith
  apply (div_le_div_iff₀ hx0 hy0).mpr
  nlinarith only [hm,mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hlog1),
    mul_nonneg (sub_nonneg.mpr hden) (sub_nonneg.mpr (log_le_log hx1 (by linarith : x-1≤ y-1)))]

theorem inner_integrable {a b : ℝ} (ha : 2≤ a) (hab : a≤ b) (hb : b≤3) :
    IntervalIntegrable (fun t : ℝ => log (t-1)/t) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  apply ContinuousOn.div
  · apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
    intro t ht
    change t-1≠0
    linarith only [ha,ht.1]
  · exact continuousOn_id
  · intro t ht
    linarith only [ha,ht.1]

theorem inner_quotient_mono {s t : ℝ} (hs : 3≤ s) (hst : s≤ t) (ht : t≤4) :
    jurkatRichertInnerIntegral s/s ≤ jurkatRichertInnerIntegral t/t := by
  let f := fun x : ℝ => log (x-1)/x
  have hs0 : 0<s := by linarith
  have ht0 : 0<t := by linarith
  have hfs : 0≤ f (s-1) := div_nonneg (log_nonneg (by linarith)) (by linarith)
  have hupper : jurkatRichertInnerIntegral s ≤ (s-3)*f (s-1) := by
    unfold jurkatRichertInnerIntegral
    calc
      _ ≤ ∫ _u in (2:ℝ)..s-1, f (s-1) :=
        intervalIntegral.integral_mono_on (by linarith)
          (inner_integrable (by norm_num) (by linarith) (by linarith)) intervalIntegrable_const
          (fun x hx => inner_integrand_mono hx.1 hx.2 (by linarith))
      _ = _ := by simp [f]; ring
  have hlower : (t-s)*f (s-1) ≤ jurkatRichertInnerIntegral t-jurkatRichertInnerIntegral s := by
    have h := intervalIntegral.integral_mono_on (show s-1≤ t-1 by linarith)
      intervalIntegrable_const (inner_integrable (by linarith) (by linarith) (by linarith))
      (fun x (hx : x∈Icc (s-1) (t-1)) => inner_integrand_mono (by linarith) hx.1 (by linarith only [hx.2,ht]))
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (inner_integrable (a:=2) (b:=s-1) (by norm_num) (by linarith) (by linarith))
      (inner_integrable (a:=s-1) (b:=t-1) (by linarith) (by linarith) (by linarith))
    simp only [intervalIntegral.integral_const] at h
    change (t-1-(s-1))*f (s-1)≤_ at h
    unfold jurkatRichertInnerIntegral
    linarith only [h,hadj]
  apply (div_le_div_iff₀ hs0 ht0).mpr
  nlinarith only [mul_nonneg (sub_nonneg.mpr hst) (sub_nonneg.mpr hupper),
    mul_nonneg hs0.le (sub_nonneg.mpr hlower),mul_nonneg (sub_nonneg.mpr hst) hfs]

theorem aux_quotient_mono {s t : ℝ} (hs : (3/2:ℝ)≤ s) (hst : s≤ t) (ht : t≤4) :
    upperFactorAux s/s ≤ upperFactorAux t/t := by
  by_cases hs3 : 3≤ s
  · simpa only [upperFactorAux,max_eq_right hs3,max_eq_right (hs3.trans hst)] using
      inner_quotient_mono hs3 hst ht
  · have hz : upperFactorAux s=0 := by
      norm_num [upperFactorAux,max_eq_left (le_of_not_ge hs3),jurkatRichertInnerIntegral]
    rw [hz,zero_div]
    exact div_nonneg (upperFactorAux_bounds ht).1 (by linarith)

theorem upper_factor_shift {s t : ℝ} (hs : (3/2:ℝ)≤ s) (hst : s≤ t) (ht : t≤4) :
    jurkatRichertMertensFactor*
      (jurkatRichertUpperLinearSieveFactor s-jurkatRichertUpperLinearSieveFactor t) ≤
      40*(t-s)/(s*t) := by
  have hs0 : 0<s := by linarith
  have ht0 : 0<t := by linarith
  have haux := aux_quotient_mono hs hst ht
  have hab : jurkatRichertMertensFactor*(2*exp eulerMascheroniConstant)=40 := by
    unfold jurkatRichertMertensFactor
    have hh : exp (-eulerMascheroniConstant)*exp eulerMascheroniConstant=1 := by
      rw [← exp_add,neg_add_cancel,exp_zero]
    nlinarith only [hh]
  have hB : 0≤ jurkatRichertMertensFactor := by unfold jurkatRichertMertensFactor; positivity
  have hmain : jurkatRichertUpperLinearSieveFactor s-jurkatRichertUpperLinearSieveFactor t ≤
      (2*exp eulerMascheroniConstant)*(t-s)/(s*t) := by
    rw [numerical_upper_factor_formula,numerical_upper_factor_formula]
    have hh := mul_le_mul_of_nonneg_left haux (show 0≤2*exp eulerMascheroniConstant by positivity)
    have heq : (2*exp eulerMascheroniConstant)/s*(1+upperFactorAux s)-
        (2*exp eulerMascheroniConstant)/t*(1+upperFactorAux t) =
        (2*exp eulerMascheroniConstant)*(t-s)/(s*t)+
        (2*exp eulerMascheroniConstant)*(upperFactorAux s/s-upperFactorAux t/t) := by field_simp; ring
    linarith only [hh,heq]
  calc
    _ ≤ jurkatRichertMertensFactor*((2*exp eulerMascheroniConstant)*(t-s)/(s*t)) :=
      mul_le_mul_of_nonneg_left hmain hB
    _ = (jurkatRichertMertensFactor*(2*exp eulerMascheroniConstant))*((t-s)/(s*t)) := by ring
    _ = _ := by rw [hab]; ring

theorem selberg_constant_cap : GRH125.selbergRemainderConstant 5≤(30000000:ℝ) := by
  have hlog : 0<log (2:ℝ) := log_pos (by norm_num)
  have hq : (2:ℝ)/log 2≤4 := (div_le_iff₀ hlog).mpr (by linarith only [log_two_gt_d9])
  have hs : panSharpConstant≤32 := by
    unfold panSharpConstant
    linarith only [pi_lt_four]
  have hshort : NumericalPanHigh.panShortConstant≤512 := by
    unfold NumericalPanHigh.panShortConstant
    linarith only [hs]
  have hlong : NumericalPanHigh.panLongConstant≤2560 := by
    unfold NumericalPanHigh.panLongConstant
    calc
      _ ≤ (16:ℝ)*32*(1+4) := by gcongr
      _ = _ := by norm_num
  have he : exp (2:ℝ)≤9 := by
    rw [show (2:ℝ)=1+1 by norm_num,exp_add]
    nlinarith only [exp_one_lt_d9,exp_pos (1:ℝ)]
  have hlong0 : 0≤ NumericalPanHigh.panLongConstant := by
    unfold NumericalPanHigh.panLongConstant
    have := panSharpConstant_pos
    positivity
  have hhigh : NumericalPanHigh.panHighConstant≤7630848 := by
    unfold NumericalPanHigh.panHighConstant NumericalPanHigh.panCellConstant
    calc
      _ ≤ (9:ℝ)*(36*512+36*9*2560) := by gcongr
      _ = _ := by norm_num
  have hU : GRH125.panUnweightedConstant 30≤30551360 := by
    unfold GRH125.panUnweightedConstant GRH125.panLedgerConstant GRH125.panPrincipalConstant
    linarith only [hhigh]
  have hU0 := (GRH125.panUnweightedConstant_pos 30).le
  have henv0 := (H30.panActualEnvelopeConstant_pos (2/log 2)).le
  have hLi : liuLogarithmicIntegralUpperConstant (2/log 2)≤10 := by
    unfold liuLogarithmicIntegralUpperConstant
    rw [abs_of_nonneg (by positivity : (0:ℝ)≤2/log 2)]
    linarith only [hq]
  have henv : H30.panActualEnvelopeConstant (2/log 2)≤26 := by
    unfold H30.panActualEnvelopeConstant liuPanLiEnvelopeConstant
    have hh : liuLogarithmicIntegralUpperConstant (2/log 2)/log 2≤20 :=
      (div_le_iff₀ hlog).mpr (by linarith only [hLi,log_two_gt_d9])
    linarith only [hh]
  have hD : GRH125.panWeightedSquareConstant 5≤(29000000:ℝ)^2 := by
    unfold GRH125.panWeightedSquareConstant
    norm_num only [GRH125.panWeightedSaving,Nat.reduceMul,Nat.reduceAdd]
    calc
      _ ≤ (2:ℝ)^20*26*30551360 := by gcongr <;> norm_num
      _ ≤ _ := by norm_num
  have hW : GRH125.panWeightedConstant 5≤29000001 := by
    unfold GRH125.panWeightedConstant
    have hh := Real.sqrt_le_iff.mpr ⟨(by norm_num : (0:ℝ)≤29000000),hD⟩
    linarith only [hh]
  have hn : GRH125.panNormalizationConstant≤1296 := by
    have hgamma : exp eulerMascheroniConstant≤3 := by
      have hh : exp eulerMascheroniConstant≤ exp 1 :=
        exp_le_exp.mpr (by linarith only [eulerMascheroniConstant_lt_two_thirds])
      exact hh.trans (by linarith only [exp_one_lt_d9])
    have hdiv : H30.panDivisorConstant≤216 := by
      unfold H30.panDivisorConstant
      calc
        _ ≤ ((2:ℝ)*3)^3 := by gcongr
        _ = _ := by norm_num
    have hdelta : |(2:ℝ)-2/log 2|≤2 := by
      rw [abs_le]
      constructor <;> linarith only [hq,div_nonneg (by norm_num : (0:ℝ)≤2) hlog.le]
    unfold GRH125.panNormalizationConstant H30.panNormalizationConstant
    calc
      _ ≤ (3:ℝ)*216*2 := by gcongr
      _ = _ := by norm_num
  have hLi2 : liuLogarithmicIntegralUpperConstant 2≤8 := by
    norm_num only [liuLogarithmicIntegralUpperConstant,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith only [hq]
  unfold GRH125.selbergRemainderConstant GRH125.panCanonicalConstant
  linarith only [hW,hn,hLi2]

#print axioms upper_factor_shift
#print axioms selberg_constant_cap
end ChenEffective.GRHJoint
