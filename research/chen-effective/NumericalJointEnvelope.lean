import NumericalQuotientEnvelope

noncomputable section
namespace ChenEffective
open Real Set
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def jointEnvelopeRadius (A : ℝ) : ℝ := 6*(1+max 0 A)^(1/8 : ℝ)
def jointEnvelopeFloor (A : ℝ) : ℝ := Real.exp (-8*jointEnvelopeRadius A*Real.log (6*jointEnvelopeRadius A))

theorem jointEnvelopeRadius_six (A : ℝ) : 6 ≤ jointEnvelopeRadius A := by
  have hh : 1 ≤ (1+max 0 A)^(1/8 : ℝ) := Real.one_le_rpow
    (by linarith only [le_max_left (0 : ℝ) A]) (by norm_num)
  unfold jointEnvelopeRadius
  linarith only [hh]

theorem jointEnvelopeFloor_pos (A : ℝ) : 0 < jointEnvelopeFloor A := Real.exp_pos _
theorem jointEnvelopeFloor_le_one (A : ℝ) : jointEnvelopeFloor A ≤ 1 := by
  have hr := jointEnvelopeRadius_six A
  apply Real.exp_le_one_iff.mpr
  have hl : 0 ≤ Real.log (6*jointEnvelopeRadius A) := Real.log_nonneg (by linarith only [hr])
  nlinarith only [mul_nonneg (by linarith only [hr] : 0 ≤ 8*jointEnvelopeRadius A) hl]

/-- The perturbation compensates for the coarse hat decay once
`s >= 6*(1+A)^(1/8)`. No separate compact minimum is taken. -/
theorem numerical_joint_envelope {H : Section13HatLayers} (hH : Section13HatContract H 2)
    {D A : ℝ} (hD : 2 ≤ D) (hA : Real.log D ≤ A) (n : ℕ) {s : ℝ} (hs : 2 ≤ s) :
    jointEnvelopeFloor A ≤ errorEnvelope H n D 16 s := by
  have hD0 : 0 < D := by linarith only [hD]
  have hL : 0 < Real.log D := Real.log_pos (by linarith only [hD])
  have hs0 : 0 < s := by linarith only [hs]
  have hR := jointEnvelopeRadius_six A
  have hhat := numerical_hat_lower_profile hH (ErrorSign.ofDepth n) hs
  have hT0 : 0 ≤ H.T (ErrorSign.ofDepth n) s := (hH.positive _ _ hs0).le
  have hP : 1 ≤ (1+s^(16 : ℝ)/Real.log D)^s := Real.one_le_rpow
    (le_add_of_nonneg_right (by positivity)) hs0.le
  unfold errorEnvelope Section13HatLayers.kappaHat
  norm_num only [sub_self,zero_add,Real.rpow_one]
  change jointEnvelopeFloor A ≤ (1+s^(16 : ℝ)/Real.log D)^s*s*H.T (ErrorSign.ofDepth n) s
  by_cases hsmall : s ≤ jointEnvelopeRadius A
  · have hlog : Real.log (6*s) ≤ Real.log (6*jointEnvelopeRadius A) :=
      Real.log_le_log (by positivity) (by linarith only [hsmall])
    have hlog0 : 0 ≤ Real.log (6*s) := Real.log_nonneg (by linarith only [hs])
    have hprod := mul_le_mul hsmall hlog hlog0 (by linarith only [hR] : 0 ≤ jointEnvelopeRadius A)
    have hlow : jointEnvelopeFloor A ≤ Real.exp (-8*s*Real.log (6*s)) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hprod]
    have hscale : 1 ≤ (1+s^(16 : ℝ)/Real.log D)^s*s := by
      have hh := mul_le_mul_of_nonneg_right hP hs0.le
      nlinarith only [hh,hs]
    exact (hlow.trans hhat).trans (by nlinarith only [mul_le_mul_of_nonneg_right hscale hT0])
  · have hlarge : jointEnvelopeRadius A ≤ s := (lt_of_not_ge hsmall).le
    have hroot : ((1+max 0 A)^(1/8 : ℝ))^8 = 1+max 0 A := by
      rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith only [le_max_left (0 : ℝ) A] : 0 ≤ 1+max 0 A)]
      norm_num
    have hpow := pow_le_pow_left₀ (by unfold jointEnvelopeRadius; positivity) hlarge 8
    have hbudget : (6 : ℝ)^8*Real.log D ≤ s^8 := by
      rw [jointEnvelopeRadius,mul_pow,hroot] at hpow
      have hh := mul_le_mul_of_nonneg_left (hA.trans (le_max_right 0 A)) (show (0 : ℝ) ≤ 6^8 by positivity)
      nlinarith only [hpow,hh]
    have hlogs := Real.log_le_log (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 6) 8) hL) hbudget
    rw [Real.log_mul (by positivity) hL.ne',Real.log_pow,Real.log_pow] at hlogs
    norm_num only [Nat.cast_ofNat] at hlogs
    have hform : (s^(16 : ℝ)/Real.log D)^s*Real.exp (-8*s*Real.log (6*s)) =
        Real.exp (s*(8*Real.log s-Real.log (Real.log D)-8*Real.log 6)) := by
      rw [Real.rpow_def_of_pos (by positivity),Real.log_div (by positivity) hL.ne',
        Real.log_rpow hs0,Real.log_mul (by norm_num) hs0.ne',← Real.exp_add]
      congr 1
      ring
    have hone : 1 ≤ (s^(16 : ℝ)/Real.log D)^s*Real.exp (-8*s*Real.log (6*s)) := by
      rw [hform]
      apply Real.one_le_exp_iff.mpr
      exact mul_nonneg hs0.le (by linarith only [hlogs])
    have hp : (s^(16 : ℝ)/Real.log D)^s ≤ (1+s^(16 : ℝ)/Real.log D)^s :=
      Real.rpow_le_rpow (by positivity) (by linarith) hs0.le
    have hcombined := mul_le_mul hp hhat (Real.exp_pos _).le (by positivity)
    have hscale := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ s by linarith only [hs])
      (show 0 ≤ (1+s^(16 : ℝ)/Real.log D)^s*H.T (ErrorSign.ofDepth n) s by positivity)
    exact (jointEnvelopeFloor_le_one A).trans (by nlinarith only [hone,hcombined,hscale])

/-- A simple displayed form of the subexponential logarithmic envelope floor. -/
theorem jointEnvelopeFloor_explicit {A : ℝ} (hA : 0 ≤ A) :
    Real.exp (-2000*(1+A)^(1/8 : ℝ)*Real.log (Real.exp 1+A)) ≤ jointEnvelopeFloor A := by
  have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp (by norm_num)
  have hb : 0 < 1+A := by positivity
  have hr : 0 ≤ (1+A)^(1/8 : ℝ) := Real.rpow_nonneg hb.le _
  have hl : 1 ≤ Real.log (Real.exp 1+A) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right hA)
  have hlog : Real.log (1+A) ≤ Real.log (Real.exp 1+A) :=
    Real.log_le_log hb (by linarith only [he])
  have h36 : Real.log (36 : ℝ) ≤ 35 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 36)
    linarith only [h]
  have heq : Real.log (6*jointEnvelopeRadius A) = Real.log 36+(1/8 : ℝ)*Real.log (1+A) := by
    unfold jointEnvelopeRadius
    rw [max_eq_right hA]
    rw [show (6 : ℝ)*(6*(1+A)^(1/8 : ℝ))=36*(1+A)^(1/8 : ℝ) by ring,
      Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hb _).ne',Real.log_rpow hb]
  have hh : Real.log (6*jointEnvelopeRadius A) ≤ 36*Real.log (Real.exp 1+A) := by
    rw [heq]
    linarith only [h36,hlog,hl]
  unfold jointEnvelopeFloor
  apply Real.exp_le_exp.mpr
  rw [jointEnvelopeRadius,max_eq_right hA]
  have hm := mul_le_mul_of_nonneg_left hh hr
  have hp := mul_nonneg hr (show 0 ≤ Real.log (Real.exp 1+A) by linarith only [hl])
  dsimp [jointEnvelopeRadius] at hm
  rw [max_eq_right hA] at hm
  nlinarith only [hm,hp]

#print axioms numerical_joint_envelope
#print axioms jointEnvelopeFloor_explicit
end ChenEffective
