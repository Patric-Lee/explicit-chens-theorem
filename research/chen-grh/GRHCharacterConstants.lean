import GRHSmoothedCharacters

/-! A completely numerical conductor dependence for the full-GRH Gaussian
character estimate. The bound is intentionally generous; it has no implicit
constant or existential threshold. -/
noncomputable section
open Real
open TernaryGoldbach.Explicit
namespace ChenEffective.GRH
set_option maxHeartbeats 3000000

private def logEnvelope (q : ℕ) : ℝ := 100 + 10 * log q

private theorem conductor_log_nonneg (q : ℕ) [NeZero q] : 0 ≤ log (q : ℝ) :=
  log_nonneg (by exact_mod_cast NeZero.pos q)

private theorem envelope_nonneg (q : ℕ) [NeZero q] : 0 ≤ logEnvelope q := by
  unfold logEnvelope
  linarith only [conductor_log_nonneg q]

private theorem log_ten_le_three : log (10 : ℝ) ≤ 3 := by
  have he : (27 / 10 : ℝ) ≤ exp 1 := by linarith only [exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10) he 3
  rw [← exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat, mul_one] at hp
  apply (log_le_iff_le_exp (by norm_num : (0 : ℝ) < 10)).mpr
  nlinarith only [hp]

private theorem BP_log_envelope (q : ℕ) [NeZero q] {t : ℝ} (ht : |t| ≤ 54) :
    log (BP q t / 0.355) ≤ logEnvelope q := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (0 : ℝ) < q := by linarith
  have hqpow : (q : ℝ)^9 * ((q : ℝ)+1) ≤ 2*(q : ℝ)^10 := by
    calc
      _ ≤ (q : ℝ)^9 * (2*q) := by gcongr; linarith
      _ = _ := by ring
  have ht0 := abs_nonneg t
  have hp : (1.25 * (|t|+11)) ^ (10 : ℝ) ≤ (100 : ℝ)^10 := by
    norm_num only [Real.rpow_natCast]
    convert pow_le_pow_left₀
      (by positivity : (0 : ℝ) ≤ 1.25 * (|t|+11))
      (show 1.25 * (|t|+11) ≤ (100 : ℝ) by linarith) 10 using 1 <;> norm_num
  have hb : BP q t / 0.355 ≤ (10 : ℝ)^30 * (q : ℝ)^10 := by
    calc
      _ = 1400*((q : ℝ)^9*((q : ℝ)+1))*(|t|+22)*
          (1.25*(|t|+11))^(10 : ℝ)/0.355 := by unfold BP; ring
      _ ≤ 1400*(2*(q : ℝ)^10)*76*((100 : ℝ)^10)/0.355 := by gcongr <;> linarith
      _ ≤ _ := by norm_num <;> nlinarith only [pow_nonneg hq0.le 10]
  have hlog := log_le_log (div_pos (BP_pos q t) (by norm_num)) hb
  rw [log_mul (by positivity) (pow_pos hq0 10).ne', log_pow, log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  unfold logEnvelope
  norm_num at hlog ⊢
  nlinarith only [hlog, log_ten_le_three]

private theorem log_ratio_three_ge : (1 : ℝ) ≤ log (10/3 : ℝ) := by
  have h := log_le_log (exp_pos 1) (show exp 1 ≤ (10/3 : ℝ) by linarith only [exp_one_lt_d9])
  rw [log_exp] at h
  exact h

private theorem log_ratio_line_ge : (1 : ℝ) ≤ log (10/2.3 : ℝ) := by
  have h := log_le_log (exp_pos 1) (show exp 1 ≤ (10/2.3 : ℝ) by linarith only [exp_one_lt_d9])
  rw [log_exp] at h
  exact h

private theorem Z3_cap (q : ℕ) [NeZero q] : Z3 q 50 ≤ logEnvelope q := by
  unfold Z3
  have h := BP_log_envelope q (t := 50) (by norm_num)
  have hd := log_ratio_three_ge
  have hk := envelope_nonneg q
  apply (div_le_iff₀ (by linarith : 0 < log (10/3 : ℝ))).mpr
  nlinarith only [h, mul_nonneg hk (sub_nonneg.mpr hd)]

private theorem ZL_cap (q : ℕ) [NeZero q] : ZL q 50 ≤ logEnvelope q := by
  unfold ZL
  have h := BP_log_envelope q (t := 50+3.48) (by norm_num)
  have hd := log_ratio_line_ge
  have hk := envelope_nonneg q
  apply (div_le_iff₀ (by linarith : 0 < log (10/2.3 : ℝ))).mpr
  nlinarith only [h, mul_nonneg hk (sub_nonneg.mpr hd)]

private theorem E0_cap (q : ℕ) [NeZero q] : E0b q ≤ 112*logEnvelope q := by
  have h := BP_log_envelope q (t := 0) (by norm_num)
  have hd := log_ratio_three_ge
  have hk := envelope_nonneg q
  have hh : log (BP q 0/0.355)/log (10/3 : ℝ) ≤ logEnvelope q :=
    (div_le_iff₀ (by linarith : 0 < log (10/3 : ℝ))).mpr
      (by nlinarith only [h, mul_nonneg hk (sub_nonneg.mpr hd)])
  exact mul_le_mul_of_nonneg_left hh (by norm_num)

private theorem E1_cap (q : ℕ) [NeZero q] : E1b q 50 ≤ 200*logEnvelope q := by
  have hj : (Jl (50 : ℝ) : ℝ) ≤ 16 := by
    unfold Jl
    have hh := Nat.floor_le (by norm_num : (0 : ℝ) ≤ 50/3.48)
    push_cast
    linarith
  have hj0 : (0 : ℝ) ≤ Jl (50 : ℝ) := Nat.cast_nonneg _
  have hs1 : √(2*π*0.6647*(2*((Jl (50 : ℝ) : ℝ)*3.48))) ≤ 100 := by
    apply (sqrt_le_iff).mpr ⟨by norm_num, ?_⟩
    calc
      2*π*0.6647*(2*((Jl (50 : ℝ) : ℝ)*3.48)) ≤ 2*4*0.6647*(2*(16*3.48)) := by gcongr <;> linarith only [pi_lt_four]
      _ ≤ (100 : ℝ)^2 := by norm_num
  have hs2 : √(2*π*0.1707*(2*((Jl (50 : ℝ) : ℝ)*3.48))) ≤ 100 := by
    apply (sqrt_le_iff).mpr ⟨by norm_num, ?_⟩
    calc
      2*π*0.1707*(2*((Jl (50 : ℝ) : ℝ)*3.48)) ≤ 2*4*0.1707*(2*(16*3.48)) := by gcongr <;> linarith only [pi_lt_four]
      _ ≤ (100 : ℝ)^2 := by norm_num
  have hf : (1/3.48 : ℝ)*√(2*π*0.6647*(2*((Jl (50 : ℝ) : ℝ)*3.48))) +
      √(2*π*0.1707*(2*((Jl (50 : ℝ) : ℝ)*3.48))) ≤ 200 := by nlinarith only [hs1,hs2]
  unfold E1b
  calc
    _ ≤ logEnvelope q * 200 :=
      mul_le_mul (ZL_cap q) hf (by positivity) (envelope_nonneg q)
    _ = _ := by ring

private theorem rhoB_cap : rhoB ≤ (3/4 : ℝ) := by
  unfold rhoB
  rw [Real.exp_neg]
  apply (inv_le_iff_one_le_mul₀ (exp_pos _)).mpr
  have h := add_one_le_exp (0.1398*4.4 : ℝ)
  nlinarith only [h]

private theorem E2_cap (q : ℕ) [NeZero q] : E2b q 50 0 ≤ 400*logEnvelope q+1600 := by
  have hk := envelope_nonneg q
  have hz := Z3_cap q
  have hc : c3 50 ≤ 1 := by
    unfold c3
    norm_num only [div_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 125*log (10/3 : ℝ))).mpr
    nlinarith only [log_ratio_three_ge]
  have hd : (1/4 : ℝ) ≤ 1-rhoB := by linarith only [rhoB_cap]
  have hd0 : 0 < 1-rhoB := by linarith
  have hd2 : (1/16 : ℝ) ≤ (1-rhoB)^2 := by nlinarith only [hd]
  have h1 : 2*Z3 q 50/(1-rhoB) ≤ 8*logEnvelope q := by
    apply (div_le_iff₀ hd0).mpr
    nlinarith only [hz, mul_nonneg hk (sub_nonneg.mpr hd)]
  have h2 : 2*c3 50/(1-rhoB)^2 ≤ 32 := by
    apply (div_le_iff₀ (sq_pos_of_pos hd0)).mpr
    nlinarith only [hc,hd2]
  have hEB : EB 50 ≤ 50 := by
    unfold EB
    have h : exp (-(0.1598*50 : ℝ)) ≤ 1 := exp_le_one_iff.mpr (by norm_num)
    nlinarith only [h]
  unfold E2b
  norm_num only [EA, ite_true, zero_mul, add_zero]
  calc
    _ ≤ 50*(8*logEnvelope q+32) :=
      mul_le_mul hEB (add_le_add h1 h2) (by
        have := Z3_nonneg q 50
        have := c3_nonneg (by norm_num : (0 : ℝ) < 50)
        positivity) (by norm_num)
    _ = _ := by ring

private theorem DN_cap (q : ℕ) [NeZero q] : DN q ≤ logEnvelope q := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hn : 0 < (512 : ℝ)*(q : ℝ)^9*((q : ℝ)+1)/0.355 := by positivity
  have harg : 512*(q : ℝ)^9*((q : ℝ)+1)/0.355 ≤ BP q 0/0.355 := by
    unfold BP
    norm_num only [abs_zero, zero_add, Real.rpow_natCast]
    have hp : (0 : ℝ) ≤ (q : ℝ)^9*((q : ℝ)+1) := by positivity
    nlinarith only [hp]
  exact (log_le_log hn harg).trans (BP_log_envelope q (t := 0) (by norm_num))

private theorem V_cap (q : ℕ) [NeZero q] :
    Vb q 0/(2*π) ≤ 8960*logEnvelope q+409920 := by
  have hk := envelope_nonneg q
  have hD := DN_cap q
  have hD0 := DN_nonneg q
  have hl2 : (2 : ℝ)/log 2 ≤ 4 := (div_le_iff₀ (log_pos (by norm_num))).mpr
    (by linarith only [Real.log_two_gt_d9])
  have hV : 0 ≤ Vb q 0 := by
    unfold Vb
    have := thetaD_pos 0
    have := log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  have hb : Vb q 0 ≤ 8960*logEnvelope q+409920 := by
    have heq : Vb q 0 = 112*(2/log 2+24/5)*((DN q+37)*(50/7)+3250/49) := by
      unfold Vb thetaD
      norm_num
      <;> ring
    rw [heq]
    calc
      _ ≤ 112*10*((logEnvelope q+37)*(50/7)+3250/49) := by gcongr <;> linarith only [hl2]
      _ ≤ _ := by norm_num <;> nlinarith only [hk]
  exact (div_le_self hV (by linarith only [Real.pi_gt_three])).trans hb

theorem gaussian_constant_cap (q : ℕ) [NeZero q] :
    gaussianCharacterConstant q ≤ (10^7 : ℝ)*(1+log q) := by
  have h0 := E0_cap q
  have h1 := E1_cap q
  have h2 := E2_cap q
  have hv := V_cap q
  unfold gaussianCharacterConstant
  unfold logEnvelope at h0 h1 h2 hv
  nlinarith only [h0,h1,h2,hv,conductor_log_nonneg q]

theorem gaussian_character_numerical {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖Ssum χ 0 x‖ ≤ (10^7 : ℝ)*(1+log q)*√x :=
  (gaussian_character_sqrt hχ hχ1 hx).trans
    (mul_le_mul_of_nonneg_right (gaussian_constant_cap q) (sqrt_nonneg x))

#print axioms gaussian_constant_cap
#print axioms gaussian_character_numerical
end ChenEffective.GRH
