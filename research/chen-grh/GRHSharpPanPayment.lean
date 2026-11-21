import GRHSharpCutoffBudget

noncomputable section
namespace ChenEffective.GRHSharp
open Real
set_option maxHeartbeats 3000000

/-- Specialize to the logarithmic degree actually used by the low moving
lane, rather than paying the old unused degree-100 box. -/
theorem pan_log_log_cap {L : ℝ} (hL : (637000:ℝ)≤L) :
    log L≤L/40000 := by
  have hl : 0<L := by linarith only [hL]
  have he := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤27/10)
    (by linarith only [exp_one_gt_d9] : (27/10:ℝ)≤exp 1) 14
  rw [← exp_nat_mul] at he
  norm_num only [Nat.cast_ofNat,mul_one] at he
  have hn : (637000:ℝ)≤(27/10:ℝ)^14 := by norm_num
  have hlog : log (637000:ℝ)≤14 := by
    have hx : (637000:ℝ)≤exp 14 := by norm_num at he; linarith only [he]
    have hh := log_le_log (by norm_num : (0:ℝ)<637000) hx
    rwa [log_exp] at hh
  have hh := log_le_sub_one_of_pos (show 0<L/637000 by positivity)
  rw [log_div hl.ne' (by norm_num : (637000:ℝ)≠0)] at hh
  linarith only [hh,hlog,hL]

theorem pan_polynomial_payment {L A α : ℝ} {k : ℕ}
    (hL : (637000:ℝ)≤L) (hA : A≤(1e17:ℝ))
    (hα : (1/512:ℝ)≤α) (hk : k≤73) :
    A*L^k*exp (-α*L)≤1 := by
  have hl : 0<L := by linarith only [hL]
  have hl1 : 1≤L := by linarith only [hL]
  have he := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤27/10)
    (by linarith only [exp_one_gt_d9] : (27/10:ℝ)≤exp 1) 40
  rw [← exp_nat_mul] at he
  norm_num only [Nat.cast_ofNat,mul_one] at he
  have hn : (1e17:ℝ)≤(27/10:ℝ)^40 := by norm_num
  have hc : (1e17:ℝ)≤exp 40 := by norm_num at he; linarith only [he]
  have hp : L^k≤exp (73*L/40000) := by
    calc
      _ ≤ L^73 := pow_le_pow_right₀ hl1 hk
      _ = exp ((73:ℝ)*log L) := by
        have hh := exp_nat_mul (log L) 73
        norm_num only [Nat.cast_ofNat] at hh
        rw [exp_log hl] at hh
        exact hh.symm
      _ ≤ _ := exp_le_exp.mpr (by linarith only [pan_log_log_cap hL])
  calc
    _ ≤ exp 40*exp (73*L/40000)*exp (-α*L) := by
      apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
      exact mul_le_mul (hA.trans hc) hp (pow_nonneg hl.le _) (exp_pos _).le
    _ = exp (40+73*L/40000-α*L) := by rw [← exp_add,← exp_add]; congr 1; ring
    _ ≤ 1 := by
      rw [← exp_zero]
      apply exp_le_exp.mpr
      nlinarith only [hL,mul_nonneg hl.le (sub_nonneg.mpr hα)]

#print axioms pan_polynomial_payment
end ChenEffective.GRHSharp
