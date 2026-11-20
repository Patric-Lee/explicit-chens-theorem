import BJSJointBudget

noncomputable section
namespace ChenEffective.H29
open Real MathlibNt.SieveTheory.SwitchingPrinciple
set_option maxHeartbeats 3000000

theorem log_three_cap : log (3:ℝ)≤6/5 := by
  have he : (27/10:ℝ)≤exp 1 := by linarith only [exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤27/10) he 6
  rw [← exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat,mul_one] at hp
  have hn : (3:ℝ)^5≤exp 6 := by nlinarith only [hp]
  have hl := log_le_log (by positivity : (0:ℝ)<3^5) hn
  rw [log_pow,log_exp] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [hl]

/-- Keep the two different decay orders after normalizing by the main scale. -/
def tripleErrorEnvelope (C L : ℝ) : ℝ := 2*C/L^3+38/L

def variableChenBudget (baseLoss mediumLoss endpointLoss K η C L : ℝ) : ChenBudget :=
  ⟨baseLoss,mediumLoss,endpointLoss,K*(0.49254+η),tripleErrorEnvelope C L⟩

theorem variable_margin (a b e K η C L : ℝ) :
    (variableChenBudget a b e K η C L).margin =
      2.6408-a-b/2-e-(K*(0.49254+η)+tripleErrorEnvelope C L)/2 := by
  unfold variableChenBudget ChenBudget.margin ChenBudget.weighted
  ring

/-- The pre-sieve contraction is paid from its actual logarithmic size. -/
theorem presieve_shift_payment {q U L δ : ℝ} (hL : 0<L)
    (hq : q≤1+2*U) (hbudget : 10*(1+2*U)≤δ*L) :
    q/((1/10:ℝ)*L)≤δ := by
  apply (div_le_iff₀ (by positivity : 0<(1/10:ℝ)*L)).mpr
  nlinarith only [hq,hbudget]

theorem variable_triple_error_payment {C x L S : ℝ}
    (hC : 0≤C) (hx : 0≤x) (hL : 0<L) (hS : (1/2:ℝ)≤S) :
    C*x/L^5+19*x/L^3 ≤ tripleErrorEnvelope C L*(S*x/L^2) := by
  let a := C/L^3+19/L
  have ha : 0≤a := by dsimp [a]; positivity
  have hp := mul_le_mul_of_nonneg_left hS (mul_nonneg (by norm_num : (0:ℝ)≤2) ha)
  have hcoef : a≤tripleErrorEnvelope C L*S := by
    calc
      a=(2*a)*(1/2) := by ring
      _ ≤ (2*a)*S := hp
      _ = tripleErrorEnvelope C L*S := by unfold tripleErrorEnvelope; dsimp [a]; ring
  have hh := mul_le_mul_of_nonneg_right hcoef (div_nonneg hx (sq_nonneg L))
  have hid : C*x/L^5+19*x/L^3=a*(x/L^2) := by
    dsimp [a]
    field_simp [hL.ne']
    <;> ring
  rw [hid]
  convert hh using 1 <;> ring

theorem variable_triple_envelope_cap {C L : ℝ}
    (hC : C≤10^34) (hL : (3*10^12:ℝ)≤L) :
    tripleErrorEnvelope C L≤1/1000 := by
  have hl : 0<L := lt_of_lt_of_le (by norm_num) hL
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3*10^12) hL 3
  have hc : C/L^3≤1/2500 := (div_le_iff₀ (pow_pos hl 3)).mpr (by nlinarith only [hp,hC])
  have hr : (19:ℝ)/L≤1/10000 := (div_le_iff₀ hl).mpr (by linarith only [hL])
  calc
    tripleErrorEnvelope C L=2*(C/L^3)+2*(19/L) := by unfold tripleErrorEnvelope; ring
    _ ≤ 2*(1/2500)+2*(1/10000) := by gcongr
    _ = 1/1000 := by norm_num

#print axioms variable_triple_error_payment
end ChenEffective.H29
