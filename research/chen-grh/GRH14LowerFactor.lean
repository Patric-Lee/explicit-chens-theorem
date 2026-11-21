import NumericalLowerFactor
import SharperSieveDensity
import NumericalBaseCandidates
import ChenBudget
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
namespace ChenEffective.GRH14
open Real Set MeasureTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem inner_integral_quarter {u : ℝ} (hu3 : 3≤u) (hu4 : u≤4) :
    0≤jurkatRichertInnerIntegral u ∧ jurkatRichertInnerIntegral u≤1/4 := by
  have hcont : ContinuousOn (fun t : ℝ => log (t-1)/t) (Icc 2 (u-1)) := by
    apply ContinuousOn.div
    · apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
      intro t ht
      change t-1≠0
      linarith only [ht.1]
    · exact continuousOn_id
    · intro t ht
      linarith only [ht.1]
  have hi := ContinuousOn.intervalIntegrable_of_Icc (μ:=volume) (show (2:ℝ)≤u-1 by linarith) hcont
  have hpoint (t : ℝ) (ht : t∈Icc 2 (u-1)) : log (t-1)/t≤(t-2)/2 := by
    have ht0 : 0<t := by linarith only [ht.1]
    have hl := log_le_sub_one_of_pos (show 0<t-1 by linarith only [ht.1])
    apply (div_le_iff₀ ht0).mpr
    nlinarith only [hl,sq_nonneg (t-2)]
  have hbound : jurkatRichertInnerIntegral u ≤ (u-3)^2/4 := by
    unfold jurkatRichertInnerIntegral
    calc
      _ ≤ ∫ t in (2:ℝ)..u-1, (t-2)/2 :=
        intervalIntegral.integral_mono_on (by linarith) hi
          (((continuous_id.sub continuous_const).div_const 2).intervalIntegrable _ _) hpoint
      _ = _ := by
        have heq : (∫ t in (2:ℝ)..u-1, t-2) =
            (∫ t in (2:ℝ)..u-1, t) - ∫ _t in (2:ℝ)..u-1, (2:ℝ) :=
          intervalIntegral.integral_sub (continuous_id.intervalIntegrable _ _) intervalIntegrable_const
        rw [intervalIntegral.integral_div,heq,integral_id,intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  refine ⟨(numerical_inner_integral hu3 hu4).1,?_⟩
  nlinarith only [hbound,hu3,hu4,mul_nonneg (show 0≤u-3 by linarith) (show 0≤4-u by linarith)]

theorem lower_factor_scaled_loss {s : ℝ} (hs : (49/10:ℝ)≤s) (hs5 : s≤5) :
    jurkatRichertMertensFactor*
      (dimensionOneLowerLinearSieveFactor 5-dimensionOneLowerLinearSieveFactor s) ≤
        (41/100:ℝ)*(5-s) := by
  let B := fun t : ℝ => log (t-1)+∫ u in (3:ℝ)..t-1, jurkatRichertInnerIntegral u/u
  have hs0 : 0<s := by linarith only [hs]
  have hsp : 0<s-1 := by linarith only [hs]
  have h3s : (3:ℝ)≤s-1 := by linarith only [hs]
  have hs4 : s-1≤(4:ℝ) := by linarith only [hs5]
  have hδ : 0≤5-s := by linarith only [hs5]
  have hi1 := numerical_outer_interval (le_refl (3:ℝ)) h3s hs4
  have hi2 := numerical_outer_interval h3s hs4 (le_refl (4:ℝ))
  have hl : log 4-log (s-1) ≤ (5-s)/(s-1) := by
    have hh := log_le_sub_one_of_pos (show 0<(4:ℝ)/(s-1) by positivity)
    rw [log_div (by norm_num) hsp.ne'] at hh
    convert hh using 1 <;> field_simp <;> ring
  have hint : (∫ u in s-1..(4:ℝ), jurkatRichertInnerIntegral u/u) ≤
      (5-s)/(4*(s-1)) := by
    calc
      _ ≤ ∫ _u in s-1..(4:ℝ), (1/4:ℝ)/(s-1) := by
        apply intervalIntegral.integral_mono_on hs4 hi2 intervalIntegrable_const
        intro u hu
        have hu0 : 0<u := by linarith only [h3s,hu.1]
        apply (div_le_div_of_nonneg_right (inner_integral_quarter (h3s.trans hu.1) hu.2).2 hu0.le).trans
        exact div_le_div_of_nonneg_left (by norm_num) hsp hu.1
      _ = _ := by simp only [intervalIntegral.integral_const,smul_eq_mul]; field_simp [hsp.ne'] <;> ring
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hsum : B 5-B s ≤ (5/4:ℝ)*(5-s)/(s-1) := by
    dsimp only [B]
    norm_num only [show (5:ℝ)-1=4 by norm_num]
    have heq : (5-s)/(s-1)+(5-s)/(4*(s-1))=(5/4:ℝ)*(5-s)/(s-1) := by field_simp [hsp.ne'] <;> ring
    linarith only [hl,hint,hadd,heq]
  have hdiff : B 5-B s ≤ (25/78:ℝ)*(5-s) := by
    apply hsum.trans
    apply (div_le_iff₀ hsp).mpr
    nlinarith only [mul_nonneg hδ (show 0≤s-49/10 by linarith only [hs])]
  have hlog39 : (27/20:ℝ)≤log (39/10:ℝ) := by
    have hh := sum_range_le_log_div (by norm_num : (0:ℝ)≤29/49)
      (by norm_num : (29/49:ℝ)<1) 3
    norm_num [Finset.sum_range_succ] at hh
    linarith only [hh]
  have hBs : (27/20:ℝ)≤B s := by
    have hlog := log_le_log (by norm_num : (0:ℝ)<39/10) (show (39/10:ℝ)≤s-1 by linarith only [hs])
    have hI : 0≤∫ u in (3:ℝ)..s-1, jurkatRichertInnerIntegral u/u := by
      apply intervalIntegral.integral_nonneg h3s
      intro u hu
      exact (numerical_outer_integrand ⟨hu.1,hu.2.trans hs4⟩).1
    dsimp only [B]
    linarith only [hlog,hlog39,hI]
  have hquot : (27/100:ℝ)≤B s/s := (le_div_iff₀ hs0).mpr (by linarith only [hBs,hs5])
  have hcompare : (27/500:ℝ)*(5-s)≤B s/s-B s/5 := by
    have hh := mul_le_mul_of_nonneg_right hquot hδ
    have heq : (B s/s)*(5-s)=5*(B s/s-B s/5) := by field_simp <;> ring
    linarith only [hh,heq]
  have hscaled : B 5/5-B s/s ≤ (41/4000:ℝ)*(5-s) := by
    nlinarith only [hdiff,hcompare,hδ]
  have hcancel : jurkatRichertMertensFactor*(2*exp eulerMascheroniConstant)=40 := by
    unfold jurkatRichertMertensFactor
    have hh : exp (-eulerMascheroniConstant)*exp eulerMascheroniConstant=1 := by
      rw [← exp_add,neg_add_cancel,exp_zero]
    nlinarith only [hh]
  calc
    _ = (jurkatRichertMertensFactor*(2*exp eulerMascheroniConstant))*(B 5/5-B s/s) := by
      unfold dimensionOneLowerLinearSieveFactor
      dsimp only [B]
      ring
    _ = 40*(B 5/5-B s/s) := by rw [hcancel]
    _ ≤ _ := by linarith only [hscaled]

theorem lower_hat_window {s : ℝ} (hs : (49/10:ℝ)≤s) :
    exp 2*sieveHat s ≤ (1/28:ℝ) := by
  have he := sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤29/10) 7
  norm_num [Finset.sum_range_succ] at he
  have he' : (120/7:ℝ)≤exp (29/10) := by linarith only [he]
  have hid : exp 2*exp (-(49/10:ℝ))*exp (29/10)=1 := by
    rw [← exp_add,← exp_add]
    norm_num
  calc
    _ ≤ exp 2*sieveHat (49/10) := mul_le_mul_of_nonneg_left (sieveHat_antitone hs) (exp_pos 2).le
    _ = (30/49)/exp (29/10) := by
      norm_num [sieveHat]
      field_simp
      nlinarith only [hid]
    _ ≤ _ := (div_le_iff₀ (exp_pos _)).mpr (by linarith only [he'])

theorem lower_factor_upper {s : ℝ} (hs : (4:ℝ)≤s) (hs5 : s≤5) :
    dimensionOneLowerLinearSieveFactor s ≤ 6 := by
  have hs0 : 0<s := by linarith only [hs]
  have h3s : (3:ℝ)≤s-1 := by linarith only [hs]
  have hs4 : s-1≤(4:ℝ) := by linarith only [hs5]
  have hI0 : 0≤∫ u in (3:ℝ)..s-1, jurkatRichertInnerIntegral u/u := by
    apply intervalIntegral.integral_nonneg h3s
    intro u hu
    exact (numerical_outer_integrand ⟨hu.1,hu.2.trans hs4⟩).1
  have hI : (∫ u in (3:ℝ)..s-1, jurkatRichertInnerIntegral u/u)≤1 := by
    calc
      _ ≤ ∫ _u in (3:ℝ)..s-1, (1:ℝ) := intervalIntegral.integral_mono_on h3s
        (numerical_outer_interval (le_refl (3:ℝ)) h3s hs4) intervalIntegrable_const
        (fun u hu => (numerical_outer_integrand ⟨hu.1,hu.2.trans hs4⟩).2)
      _ = s-4 := by simp; ring
      _ ≤ 1 := by linarith only [hs5]
  have hlog0 : 0≤log (s-1) := log_nonneg (by linarith only [hs])
  have hlog : log (s-1)≤3 := (log_le_sub_one_of_pos (by linarith only [hs])).trans (by linarith only [hs5])
  have he : exp eulerMascheroniConstant≤3 :=
    (exp_le_exp.mpr (eulerMascheroniConstant_lt_two_thirds.le.trans (by norm_num))).trans
      (exp_one_lt_d9.le.trans (by norm_num))
  have hquot : 2*exp eulerMascheroniConstant/s≤3/2 :=
    (div_le_iff₀ hs0).mpr (by linarith only [he,hs])
  unfold dimensionOneLowerLinearSieveFactor
  apply (mul_le_mul hquot (show log (s-1)+(∫ u in (3:ℝ)..s-1, jurkatRichertInnerIntegral u/u)≤4 by linarith only [hlog,hI])
    (by linarith only [hlog0,hI0]) (by norm_num)).trans
  norm_num

theorem mertens_factor_lower_one : (1:ℝ)≤jurkatRichertMertensFactor := by
  have he : exp eulerMascheroniConstant≤3 :=
    (exp_le_exp.mpr (eulerMascheroniConstant_lt_two_thirds.le.trans (by norm_num))).trans
      (exp_one_lt_d9.le.trans (by norm_num))
  have hb : 0≤jurkatRichertMertensFactor := by unfold jurkatRichertMertensFactor; positivity
  have hc : jurkatRichertMertensFactor*exp eulerMascheroniConstant=20 := by
    unfold jurkatRichertMertensFactor
    rw [mul_assoc,← exp_add,neg_add_cancel,exp_zero,mul_one]
  have hh := mul_le_mul_of_nonneg_left he hb
  linarith only [hh,hc]

theorem lower_density_budget {s : ℝ} (hs : (4929/1000:ℝ)≤s) (hs5 : s≤5) :
    jurkatRichertBaseMainCoefficient jurkatRichertJ-(27/500:ℝ) ≤
      jurkatRichertMertensFactor*(dimensionOneLowerLinearSieveFactor s-
        110*(1/2000:ℝ)*exp 2*sieveHat s) := by
  have hscaled := lower_factor_scaled_loss (show (49/10:ℝ)≤s by linarith only [hs]) hs5
  have hhat := lower_hat_window (show (49/10:ℝ)≤s by linarith only [hs])
  have hBpos : 0≤jurkatRichertMertensFactor := by unfold jurkatRichertMertensFactor; positivity
  have hh := mul_le_mul budget_mertens_factor_cap hhat
    (mul_nonneg (exp_pos 2).le (sieveHat_pos s).le) (by norm_num : (0:ℝ)≤25/2)
  rw [dimensionOneLowerLinearSieveFactor_five] at hscaled
  have hab := jurkatRichert_sieveFactor_mul_mertensFactor
  nlinarith only [hscaled,hh,hs,hs5,hab]

#print axioms lower_density_budget
#print axioms lower_factor_scaled_loss
#print axioms lower_hat_window
end ChenEffective.GRH14
