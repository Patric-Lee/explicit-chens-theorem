import GRH14ErrorBudget
import BJSH30PanQuotient

noncomputable section
namespace ChenEffective.GRH14
open Real
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem pan_log_log_cap {L : ℝ} (hL : (1000000:ℝ) ≤ L) :
    log L ≤ L/60000 := by
  have hl : 0<L := by linarith only [hL]
  have he := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2.7182818283) exp_one_gt_d9.le 14
  rw [← exp_nat_mul] at he
  norm_num only [Nat.cast_ofNat,mul_one] at he
  have hnum : (1000000:ℝ) ≤ (2.7182818283:ℝ)^14 := by norm_num
  have hlog : log (1000000:ℝ) ≤ 14 := by
    have hx : (1000000:ℝ)≤exp 14 := by
      norm_num at hnum
      linarith only [hnum,he]
    have hh := log_le_log (by norm_num : (0:ℝ)<1000000) hx
    rwa [log_exp] at hh
  have hh := log_le_sub_one_of_pos (show 0<L/1000000 by positivity)
  rw [log_div hl.ne' (by norm_num : (1000000:ℝ)≠0)] at hh
  linarith only [hh,hlog,hL]

/-- At the target, a power saving pays for all logarithmic losses used in
the low-conductor moving endpoint, without the old exponential-in-b threshold. -/
theorem pan_polynomial_payment {L A α : ℝ} {k : ℕ}
    (hL : (1000000:ℝ) ≤ L) (hA : A ≤ (1e20:ℝ))
    (hα : (1/512:ℝ) ≤ α) (hk : k ≤ 100) :
    A*L^k*exp (-α*L) ≤ 1 := by
  have hl : 0<L := by linarith only [hL]
  have hl1 : 1≤L := by linarith only [hL]
  have he := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) (by linarith only [exp_one_gt_d9] : (2:ℝ)≤exp 1) 100
  rw [← exp_nat_mul] at he
  norm_num only [Nat.cast_ofNat,mul_one] at he
  have hc : (1e20:ℝ) ≤ exp 100 := by linarith only [he]
  have hp : L^k ≤ exp (L/600) := by
    calc
      _ ≤ L^100 := pow_le_pow_right₀ hl1 hk
      _ = exp ((100:ℝ)*log L) := by
        have hh := exp_nat_mul (log L) 100
        norm_num only [Nat.cast_ofNat] at hh
        rw [exp_log hl] at hh
        exact hh.symm
      _ ≤ exp (L/600) := by
        apply exp_le_exp.mpr
        linarith only [pan_log_log_cap hL]
  calc
    _ ≤ exp 100*exp (L/600)*exp (-α*L) := by
      apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
      exact mul_le_mul (hA.trans hc) hp (pow_nonneg hl.le _) (exp_pos _).le
    _ = exp (100+L/600-α*L) := by rw [← exp_add,← exp_add]; congr 1; ring
    _ ≤ 1 := by
      rw [← exp_zero]
      apply exp_le_exp.mpr
      nlinarith only [hL,mul_nonneg hl.le (sub_nonneg.mpr hα)]

theorem pan_quotient_at_target {N : ℕ} (hN : targetCutoff ≤ N)
    {a : ℕ} (ha : 1≤a) (haN : (a:ℝ) ≤ (N:ℝ)^(2/3:ℝ)) :
    (N:ℝ)^(1/4:ℝ) ≤ (N/a:ℕ) ∧
    (1000000/4:ℝ) ≤ log (N/a:ℕ) ∧ log (N/a:ℕ) ≤ log (N:ℝ) := by
  have hL := target_log_lower hN
  have hn : 0<N := by
    by_contra h
    have hh : N=0 := by omega
    subst N
    norm_num at hL
  have hnR : (0:ℝ)<N := by exact_mod_cast hn
  have hlarge : 4096≤N := by
    have hh := log_le_sub_one_of_pos hnR
    exact_mod_cast (by linarith only [hL,hh] : (4096:ℝ)≤N)
  have ht := H30.numerical_nat_div_quarter hlarge a ha haN
  have ht0 : (0:ℝ)<(N/a:ℕ) := (rpow_pos_of_pos hnR _).trans_le ht
  have hh := log_le_log (rpow_pos_of_pos hnR (1/4:ℝ)) ht
  rw [log_rpow hnR] at hh
  refine ⟨ht,by linarith only [hh,hL],?_⟩
  exact log_le_log ht0 (by exact_mod_cast (Nat.div_le_self N a))

#print axioms pan_polynomial_payment
end ChenEffective.GRH14





