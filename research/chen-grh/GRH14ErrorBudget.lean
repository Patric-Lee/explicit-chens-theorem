import ExplicitLogBounds

/-!
Numerical target and error payments for the GRH route. All statements in
this file use only standard Lean axioms. The separate GRH14ScalarBudget adapter takes actual counting estimates as
explicit premises. No completed H=14 Chen theorem is asserted here.
-/
noncomputable section
open Real
namespace ChenEffective.GRH14
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

private opaque exponentCertificate : {n : ℕ // n = 1000000} := ⟨1000000, rfl⟩
def targetExponent : ℕ := exponentCertificate.1
theorem targetExponent_eq : targetExponent = 1000000 := exponentCertificate.2
def targetCutoff : ℕ := 3 ^ targetExponent
theorem targetCutoff_eq : targetCutoff = 3^1000000 := by
  unfold targetCutoff
  rw [targetExponent_eq]

private theorem log_three_cap : log (3 : ℝ) ≤ 6/5 := by
  have he : (27/10 : ℝ) ≤ exp 1 := by linarith only [exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27/10) he 6
  rw [← exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat, mul_one] at hp
  have hn : (3 : ℝ)^5 ≤ exp 6 := by nlinarith only [hp]
  have hl := log_le_log (by positivity : (0 : ℝ) < 3^5) hn
  rw [log_pow, log_exp] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [hl]

theorem targetCutoff_lt_double_exp_14 :
    (targetCutoff : ℝ) < exp (exp (14 : ℝ)) := by
  have he : (2.7182818283 : ℝ) ≤ exp 1 := exp_one_gt_d9.le
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283) he 14
  rw [← exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat, mul_one] at hp
  have hn : (1200000 : ℝ) < (2.7182818283 : ℝ)^14 := by norm_num
  have hlog : log (targetCutoff : ℝ) < exp 14 := by
    simp only [targetCutoff, Nat.cast_pow, Nat.cast_ofNat, log_pow]
    rw [targetExponent_eq]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hp, hn, log_three_cap]
  have htpos : (0 : ℝ) < targetCutoff := by
    exact_mod_cast (show 0 < targetCutoff by unfold targetCutoff; positivity)
  apply (log_lt_log_iff htpos (exp_pos (exp (14 : ℝ)))).mp
  rw [log_exp]
  exact hlog

theorem target_log_lower {N : ℕ} (hN : targetCutoff ≤ N) :
    (1000000 : ℝ) ≤ log (N : ℝ) := by
  have h := log_ge_power_three (b := targetExponent) (N := N) hN
  rw [targetExponent_eq] at h
  exact_mod_cast h

/-- A log-polynomial error is paid already at the proposed H<14 target. -/
theorem log_twelve_payment {L : ℝ} (hL : (1000000 : ℝ) ≤ L) :
    L^12 ≤ (1e-13 : ℝ)*exp (L/5000) := by
  have hL0 : 0 ≤ L := by linarith
  have he := pow_div_factorial_le_exp (x := L/5000) (by positivity) 200
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1000000) hL 188
  have hn : (5000 : ℝ)^200*(Nat.factorial 200 : ℝ) ≤
      (1e-13 : ℝ)*(1000000 : ℝ)^188 := by norm_num [Nat.factorial]
  have hD : (0 : ℝ) < (5000 : ℝ)^200*(Nat.factorial 200 : ℝ) := by positivity
  have hratio : (1 : ℝ) ≤ (1e-13 : ℝ)*L^188/
      ((5000 : ℝ)^200*(Nat.factorial 200 : ℝ)) := by
    apply (le_div_iff₀ hD).mpr
    nlinarith only [hp, hn]
  have hid : (L/5000)^200/(Nat.factorial 200 : ℝ) =
      L^12*L^188/((5000 : ℝ)^200*(Nat.factorial 200 : ℝ)) := by
    rw [div_pow, div_div]
    ring
  calc
    L^12 = L^12*1 := by ring
    _ ≤ L^12*((1e-13 : ℝ)*L^188/((5000 : ℝ)^200*(Nat.factorial 200 : ℝ))) :=
      mul_le_mul_of_nonneg_left hratio (pow_nonneg hL0 12)
    _ = (1e-13 : ℝ)*((L/5000)^200/(Nat.factorial 200 : ℝ)) := by rw [hid]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by norm_num)

theorem polynomial_error_payment {L C α : ℝ} {k : ℕ}
    (hL : (1000000 : ℝ) ≤ L) (hC : C ≤ (10^7 : ℝ))
    (hα : (1/5000 : ℝ) ≤ α) (hk : k ≤ 12) :
    C*L^k*exp (-α*L) ≤ (1e-6 : ℝ) := by
  have hL0 : 0 ≤ L := by linarith
  have hpow : L^k ≤ L^12 := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ L) hk
  have hexp : exp (-α*L) ≤ exp (-L/5000) :=
    exp_le_exp.mpr (by nlinarith only [mul_nonneg hL0 (sub_nonneg.mpr hα)])
  have hbase := mul_le_mul_of_nonneg_right (log_twelve_payment hL) (exp_pos (-L/5000)).le
  have hexpCancel : exp (L/5000)*exp (-L/5000) = 1 := by
    rw [← exp_add, show L/5000+ -L/5000 = 0 by ring, exp_zero]
  rw [mul_assoc, hexpCancel, mul_one] at hbase
  have hsmall : L^k*exp (-α*L) ≤ (1e-13 : ℝ) :=
    (mul_le_mul hpow hexp (exp_pos _).le (pow_nonneg hL0 12)).trans hbase
  calc
    _ = C*(L^k*exp (-α*L)) := by ring
    _ ≤ (10^7 : ℝ)*(L^k*exp (-α*L)) :=
      mul_le_mul_of_nonneg_right hC (by positivity)
    _ ≤ (10^7 : ℝ)*(1e-13 : ℝ) := mul_le_mul_of_nonneg_left hsmall (by norm_num)
    _ = _ := by norm_num

/-- A budget allowing the explicit GRH distribution constants. -/
theorem distribution_error_payment {L C α : ℝ} {k : ℕ}
    (hL : (1000000 : ℝ) ≤ L) (hC : C ≤ (1e30 : ℝ))
    (hα : (1/1000 : ℝ) ≤ α) (hk : k ≤ 12) :
    C*L^k*exp (-α*L) ≤ (1e-6 : ℝ) := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hsmall : (1e7:ℝ)*L^k*exp (-L/5000) ≤ (1e-6:ℝ) := by
    have hh := polynomial_error_payment hL (C := 1e7) (by norm_num)
      (α := 1/5000) le_rfl hk
    simpa only [show -(1/5000:ℝ)*L = -L/5000 by ring] using hh
  have he : (1e23:ℝ) ≤ exp 800 := by
    have hh := pow_div_factorial_le_exp (x := (800:ℝ)) (by norm_num) 20
    have hn : (1e23:ℝ) ≤ (800:ℝ)^20/(Nat.factorial 20:ℝ) := by norm_num [Nat.factorial]
    exact hn.trans hh
  have hpay : (1e23:ℝ)*exp (-800) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right he (exp_pos (-800:ℝ)).le
    rw [← exp_add] at hh
    norm_num at hh
    convert hh using 1 <;> norm_num
  have hextra : exp (-(α-1/5000)*L) ≤ exp (-800:ℝ) := by
    apply exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hα hL0
    nlinarith only [hh,hL]
  have hid : exp (-α*L) = exp (-L/5000)*exp (-(α-1/5000)*L) := by
    rw [← exp_add]
    congr 1
    ring
  calc
    _ ≤ (1e30:ℝ)*L^k*exp (-α*L) := by gcongr
    _ = (1e23:ℝ)*((1e7:ℝ)*L^k*exp (-L/5000))*exp (-(α-1/5000)*L) := by rw [hid]; ring
    _ ≤ (1e23:ℝ)*(1e-6:ℝ)*exp (-800:ℝ) := by gcongr
    _ ≤ _ := by nlinarith only [hpay]

/-- The old all-interval allowance cannot simply be kept at a start of 1500.
The prime 1543 alone already exceeds it on the interval [1543,1544). -/
theorem small_start_requires_larger_product_allowance :
    ((1+1/4000:ℝ)*Real.log 1544)/Real.log 1543 < (1542/1541:ℝ) := by
  have hl : (4:ℝ) ≤ Real.log 1543 := by
    exact_mod_cast (log_ge_power_three (b := 4) (N := 1543) (by norm_num))
  have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<1544/1543)
  rw [Real.log_div (by norm_num) (by norm_num)] at hh
  apply (div_lt_iff₀ (by linarith only [hl])).mpr
  nlinarith only [hl,hh]

#print axioms targetCutoff_lt_double_exp_14
#print axioms distribution_error_payment
#print axioms small_start_requires_larger_product_allowance
end ChenEffective.GRH14
