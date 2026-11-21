import GRH14ErrorBudget

noncomputable section
namespace ChenEffective.GRH14
open Real
set_option maxHeartbeats 3000000

/-- The fixed small-prime moment is affordable after truncating at roughly
N^(1/200). The factor exp(2126) is a proved divisor-moment cap, not an
extra numerical premise in the source moment theorem. -/
theorem truncated_moment_decay {L : ℝ} {C : ℕ}
    (hL : (1000000:ℝ) ≤ L) (hC : 0 < C)
    (hlogC : L/200-log 2 ≤ log (C:ℝ)) :
    exp 2126/sqrt (C:ℝ) ≤ exp (-(37/100000:ℝ)*L) := by
  have hCp : (0:ℝ) < C := by exact_mod_cast hC
  have hroot : 1/sqrt (C:ℝ)=exp (-log (C:ℝ)/2) := by
    rw [sqrt_eq_rpow,rpow_def_of_pos hCp,one_div,← exp_neg]
    congr 1
    ring
  have hl2 : log (2:ℝ) ≤ 1 := by
    linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  calc
    _ = exp (2126-log (C:ℝ)/2) := by
      rw [div_eq_mul_one_div,hroot,← exp_add]
      congr 1
      ring
    _ ≤ _ := exp_le_exp.mpr (by linarith only [hlogC,hL,hl2])

/-- A weaker exponential saving than the original AP payment still
absorbs the explicit constants at the same target. -/
theorem truncated_polynomial_payment {L A α : ℝ} {k : ℕ}
    (hL : (1000000:ℝ) ≤ L) (hA : A ≤ (1e30:ℝ))
    (hα : (3/10000:ℝ) ≤ α) (hk : k ≤ 12) :
    A*L^k*exp (-α*L) ≤ (1e-6:ℝ) := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hsmall : (1e7:ℝ)*L^k*exp (-L/5000) ≤ (1e-6:ℝ) := by
    have hh := polynomial_error_payment hL (C:=1e7) (by norm_num)
      (α:=1/5000) le_rfl hk
    simpa only [show -(1/5000:ℝ)*L = -L/5000 by ring] using hh
  have he : (1e23:ℝ) ≤ exp 100 := by
    have hh := pow_div_factorial_le_exp (x:=(100:ℝ)) (by norm_num) 40
    have hn : (1e23:ℝ) ≤ (100:ℝ)^40/(Nat.factorial 40:ℝ) := by
      norm_num [Nat.factorial]
    exact hn.trans hh
  have hpay : (1e23:ℝ)*exp (-100) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right he (exp_pos (-100:ℝ)).le
    rw [← exp_add] at hh
    norm_num at hh
    convert hh using 1 <;> norm_num
  have hextra : exp (-(α-1/5000)*L) ≤ exp (-100:ℝ) := by
    apply exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hα hL0
    nlinarith only [hh,hL]
  have hid : exp (-α*L)=exp (-L/5000)*exp (-(α-1/5000)*L) := by
    rw [← exp_add]
    congr 1
    ring
  calc
    _ ≤ (1e30:ℝ)*L^k*exp (-α*L) := by gcongr
    _ = (1e23:ℝ)*((1e7:ℝ)*L^k*exp (-L/5000))*exp (-(α-1/5000)*L) := by
      rw [hid]
      ring
    _ ≤ (1e23:ℝ)*(1e-6:ℝ)*exp (-100:ℝ) := by gcongr
    _ ≤ _ := by nlinarith only [hpay]

noncomputable def preSieveTruncation (N : ℕ) : ℕ :=
  Nat.floor ((N:ℝ)^(1/200:ℝ))

theorem truncation_log_lower {N : ℕ} (hN : targetCutoff ≤ N) :
    0 < preSieveTruncation N ∧
    log (N:ℝ)/200-log 2 ≤ log (preSieveTruncation N:ℝ) := by
  have hL := target_log_lower hN
  have hn : 0 < N := lt_of_lt_of_le (by unfold targetCutoff; positivity) hN
  have hnR : (0:ℝ) < N := by exact_mod_cast hn
  let x := (N:ℝ)^(1/200:ℝ)
  have hx : 0 < x := rpow_pos_of_pos hnR _
  have hlogx : log x=log (N:ℝ)/200 := by
    dsimp only [x]
    rw [log_rpow hnR]
    ring
  have hl2 : log (2:ℝ) ≤ 1 := by
    linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have hx2 : (2:ℝ) ≤ x := by
    apply (log_le_log_iff (by norm_num : (0:ℝ) < 2) hx).mp
    rw [hlogx]
    linarith only [hL,hl2]
  have hc : 0 < preSieveTruncation N := Nat.floor_pos.mpr (by linarith only [hx2])
  have hf : x < (preSieveTruncation N:ℝ)+1 := Nat.lt_floor_add_one x
  have hhalf : x/2 ≤ (preSieveTruncation N:ℝ) := by linarith only [hf,hx2]
  refine ⟨hc,?_⟩
  have hh := log_le_log (div_pos hx (by norm_num)) hhalf
  rw [log_div hx.ne' (by norm_num),hlogx] at hh
  exact hh

theorem truncation_tail_at_target {N : ℕ} (hN : targetCutoff ≤ N) :
    exp 2126/sqrt (preSieveTruncation N:ℝ) ≤
      exp (-(37/100000:ℝ)*log (N:ℝ)) :=
  truncated_moment_decay (target_log_lower hN) (truncation_log_lower hN).1
    (truncation_log_lower hN).2

#print axioms truncation_tail_at_target
#print axioms truncated_moment_decay
#print axioms truncated_polynomial_payment
end ChenEffective.GRH14
