import GRHQuarterMomentKernel
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-! Analytic soundness of the integer root and exponential certificates. -/
noncomputable section
namespace ChenEffective.H10Band
open Real Finset QuarterCert
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

def quarterRoot (x : ℝ) : ℝ := sqrt (sqrt x)

theorem quarterRoot_nonneg (x : ℝ) : 0≤quarterRoot x := sqrt_nonneg _
theorem quarterRoot_pos {x : ℝ} (h : 0<x) : 0<quarterRoot x :=
  sqrt_pos.mpr (sqrt_pos.mpr h)
theorem quarterRoot_fourth {x : ℝ} (h : 0≤x) : quarterRoot x^4=x := by
  have h₁ := sq_sqrt (sqrt_nonneg x)
  have h₂ := sq_sqrt h
  change (sqrt (sqrt x))^4=x
  calc
    _ = ((sqrt (sqrt x))^2)^2 := by ring
    _ = x := by rw [h₁,h₂]

theorem certified_root_lower {lo p u : ℕ} (hu : 0<u)
    (hroot : u^4≤lo*QuarterCert.scale^4) (hlp : lo≤p) :
    (u:ℝ)/QuarterCert.scale≤quarterRoot (p:ℝ) := by
  have hs : (0:ℝ)<QuarterCert.scale := by norm_num [QuarterCert.scale]
  have hr : (0:ℝ)≤(u:ℝ)/QuarterCert.scale := by positivity
  have hcast : (u:ℝ)^4≤(lo:ℝ)*(QuarterCert.scale:ℝ)^4 := by exact_mod_cast hroot
  have hp : (lo:ℝ)≤p := by exact_mod_cast hlp
  have h4 : ((u:ℝ)/QuarterCert.scale)^4≤(p:ℝ) := by
    rw [div_pow]
    apply (div_le_iff₀ (pow_pos hs 4)).mpr
    exact hcast.trans (mul_le_mul_of_nonneg_right hp (pow_nonneg hs.le 4))
  have h2 := sqrt_le_sqrt h4
  rw [show (((u:ℝ)/QuarterCert.scale)^4)=(((u:ℝ)/QuarterCert.scale)^2)^2 by ring,
    sqrt_sq (sq_nonneg _)] at h2
  have h1 := sqrt_le_sqrt h2
  rw [sqrt_sq hr] at h1
  exact h1

theorem exp3_of_integer_check {a b d t : ℕ} (hb : 0<b) (hd : 0<d)
    (h : 6*d^3*a≤(6*t*d^2+3*t^2*d+t^3)*b) :
    1+(a:ℝ)/b≤exp ((t:ℝ)/d) := by
  have hbR : (0:ℝ)<b := by exact_mod_cast hb
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hR : (6:ℝ)*d^3*a≤(6*t*d^2+3*t^2*d+t^3)*b := by exact_mod_cast h
  have hp : 1+(a:ℝ)/b≤1+(t:ℝ)/d+((t:ℝ)/d)^2/2+((t:ℝ)/d)^3/6 := by
    field_simp
    nlinarith only [hR]
  have he := sum_le_exp_of_nonneg (by positivity : (0:ℝ)≤(t:ℝ)/d) 4
  norm_num [Finset.sum_range_succ] at he
  exact hp.trans (by convert he using 1 <;> ring)

theorem exp7_of_integer_check {a b d t : ℕ} (hb : 0<b) (hd : 0<d)
    (h : 5040*d^7*a≤
      (5040*t*d^6+2520*t^2*d^5+840*t^3*d^4+210*t^4*d^3+
        42*t^5*d^2+7*t^6*d+t^7)*b) :
    1+(a:ℝ)/b≤exp ((t:ℝ)/d) := by
  have hbR : (0:ℝ)<b := by exact_mod_cast hb
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hR : (5040:ℝ)*d^7*a≤
      (5040*t*d^6+2520*t^2*d^5+840*t^3*d^4+210*t^4*d^3+
        42*t^5*d^2+7*t^6*d+t^7)*b := by exact_mod_cast h
  have hp : 1+(a:ℝ)/b≤1+(t:ℝ)/d+((t:ℝ)/d)^2/2+((t:ℝ)/d)^3/6+
      ((t:ℝ)/d)^4/24+((t:ℝ)/d)^5/120+((t:ℝ)/d)^6/720+((t:ℝ)/d)^7/5040 := by
    field_simp
    nlinarith only [hR]
  have he := sum_le_exp_of_nonneg (by positivity : (0:ℝ)≤(t:ℝ)/d) 8
  norm_num [Finset.sum_range_succ] at he
  exact hp.trans (by convert he using 1 <;> ring)

def primeEnvelope (p : ℕ) : ℝ :=
  log (1+(if p≤100 then (126/100:ℝ) else 101/100)/quarterRoot (p:ℝ)^3+
    (if p=3 then 1/quarterRoot (p:ℝ) else 0))

theorem primeEnvelope_nonneg {p : ℕ} (hp : 0<p) : 0≤primeEnvelope p := by
  unfold primeEnvelope
  apply log_nonneg
  have hq : 0<quarterRoot (p:ℝ) := quarterRoot_pos (by exact_mod_cast hp)
  have hn : 0≤(if p≤100 then (126/100:ℝ) else 101/100)/quarterRoot (p:ℝ)^3+
      (if p=3 then 1/quarterRoot (p:ℝ) else 0) := by split_ifs <;> positivity
  linarith only [hn]

theorem checked_log_majorant {lo u t degree : ℕ} (hu : 0<u)
    (hdeg : degree=3 ∨ degree=7)
    (h : factorialFor degree*denominator^degree*majorantNumerator lo u≤
      expNumerator degree t*majorantDenominator u) :
    log (1+(majorantNumerator lo u:ℝ)/majorantDenominator u)≤(t:ℝ)/denominator := by
  have hb : 0<majorantDenominator u := by unfold majorantDenominator; positivity
  have hd : 0<denominator := by norm_num [denominator]
  have he : 1+(majorantNumerator lo u:ℝ)/majorantDenominator u≤exp ((t:ℝ)/denominator) := by
    rcases hdeg with h3|h7
    · subst degree
      apply exp3_of_integer_check hb hd
      simpa [factorialFor,expNumerator] using h
    · subst degree
      apply exp7_of_integer_check hb hd
      simpa [factorialFor,expNumerator] using h
  have hl := log_le_log (by positivity : (0:ℝ)<1+(majorantNumerator lo u:ℝ)/majorantDenominator u) he
  simpa only [log_exp] using hl

theorem envelope_argument_le {lo p u : ℕ} (hlo : 3≤lo) (hlp : lo≤p) (hu : 0<u)
    (hroot : u^4≤lo*scale^4) :
    (if p≤100 then (126/100:ℝ) else 101/100)/quarterRoot (p:ℝ)^3+
      (if p=3 then 1/quarterRoot (p:ℝ) else 0)≤
      (majorantNumerator lo u:ℝ)/majorantDenominator u := by
  let r : ℝ := (u:ℝ)/scale
  have hr : 0<r := by
    dsimp only [r]
    exact div_pos (by exact_mod_cast hu) (by norm_num [scale])
  have hq := certified_root_lower hu hroot hlp
  change r≤quarterRoot (p:ℝ) at hq
  have hqp : 0<quarterRoot (p:ℝ) := hr.trans_le hq
  have hc : (if p≤100 then (126/100:ℝ) else 101/100)≤
      (if lo≤100 then (126/100:ℝ) else 101/100) := by
    split_ifs <;> norm_num <;> omega
  have hpow : r^3≤quarterRoot (p:ℝ)^3 := by gcongr
  have hi3 := one_div_le_one_div_of_le (pow_pos hr 3) hpow
  have hi1 := one_div_le_one_div_of_le hr hq
  have hm := mul_le_mul hc hi3 (by positivity : (0:ℝ)≤1/quarterRoot (p:ℝ)^3)
    (by split_ifs <;> norm_num : (0:ℝ)≤ if lo≤100 then 126/100 else 101/100)
  have hspecial : (if p=3 then 1/quarterRoot (p:ℝ) else 0)≤
      (if lo=3 then 1/r else 0) := by
    by_cases hp : p=3
    · have hl : lo=3 := by omega
      simpa only [if_pos hp,if_pos hl] using hi1
    · simp only [if_neg hp]
      split_ifs <;> positivity
  have heq : (majorantNumerator lo u:ℝ)/majorantDenominator u=
      (if lo≤100 then (126/100:ℝ) else 101/100)/r^3+(if lo=3 then 1/r else 0) := by
    unfold majorantNumerator majorantDenominator
    dsimp only [r]
    push_cast
    split_ifs <;> field_simp [show (u:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt hu),scale] <;> ring
  rw [heq]
  simp only [mul_one_div] at hm
  exact add_le_add hm hspecial

theorem primeEnvelope_le_checked {lo p u t degree : ℕ} (hlo : 3≤lo) (hlp : lo≤p)
    (hu : 0<u) (hroot : u^4≤lo*scale^4) (hdeg : degree=3 ∨ degree=7)
    (hcheck : factorialFor degree*denominator^degree*majorantNumerator lo u≤
      expNumerator degree t*majorantDenominator u) :
    primeEnvelope p≤(t:ℝ)/denominator := by
  have hq : 0<quarterRoot (p:ℝ) := quarterRoot_pos (by exact_mod_cast (by omega : 0<p))
  have harg := envelope_argument_le hlo hlp hu hroot
  have hpos : (0:ℝ)<1+(if p≤100 then (126/100:ℝ) else 101/100)/quarterRoot (p:ℝ)^3+
      (if p=3 then 1/quarterRoot (p:ℝ) else 0) := by split_ifs <;> positivity
  unfold primeEnvelope
  exact (log_le_log hpos (by linarith only [harg])).trans (checked_log_majorant hu hdeg hcheck)

#print axioms primeEnvelope_le_checked
#print axioms certified_root_lower
#print axioms exp3_of_integer_check
#print axioms exp7_of_integer_check
end ChenEffective.H10Band
end
