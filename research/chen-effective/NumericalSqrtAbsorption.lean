import NumericalSuzukiHat
import Mathlib.Data.Nat.Sqrt

namespace ChenEffective
open Real
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem numerical_exp_sqrt_round_bound {K : ℝ} {k : ℕ} (_hk : 1 ≤ k) (hK : K ≤ k) :
    Real.exp (Real.sqrt K) ≤ (3 : ℝ) ^ (Nat.sqrt k + 1) := by
  have hsq : (k : ℝ) ≤ ((Nat.sqrt k + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast (Nat.lt_succ_sqrt' k).le
  have hs : Real.sqrt K ≤ ((Nat.sqrt k + 1 : ℕ) : ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity, hK.trans hsq⟩
  calc
    _ ≤ Real.exp ((Nat.sqrt k + 1 : ℕ) : ℝ) := Real.exp_le_exp.mpr hs
    _ = (Real.exp 1) ^ (Nat.sqrt k + 1) := by rw [← Real.exp_nat_mul, mul_one]
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos 1).le
      (Real.exp_one_lt_d9.le.trans (by norm_num)) _

def sqrtSuzukiAmplitudeCap (c k : ℕ) : ℕ := 20 * c * 3 ^ (Nat.sqrt k + 1)

theorem sqrtSuzukiAmplitudeCap_le {c k : ℕ} (hk : 2 ≤ k) :
    sqrtSuzukiAmplitudeCap c k ≤ suzukiAmplitudeCap c k := by
  unfold sqrtSuzukiAmplitudeCap suzukiAmplitudeCap
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_right (by norm_num)
  have hh := Nat.sqrt_lt_self (show 1 < k by omega)
  omega

theorem numerical_sqrt_suzuki_error_at_level {D c k r : ℕ} {C K s : ℝ}
    (hD : suzukiScalarThreshold (sqrtSuzukiAmplitudeCap c k) r ≤ D)
    (hk : 1 ≤ k) (hr : 0 < r) (hC0 : 0 ≤ C) (hC : C ≤ c) (hK : K ≤ k)
    (hs : 2 ≤ s) (hs5 : s ≤ 5) (depth : ℕ) :
    C * Real.exp (Real.sqrt K) * errorEnvelope jr1965Section13HatLayers depth D 16 s *
      (Real.log D) ^ (-(1 / 2 : ℝ)) < 1 / (r : ℝ) := by
  let sign := ErrorSign.ofDepth depth
  let a := C * Real.exp (Real.sqrt K) * (s * jr1965Section13HatLayers.T sign s)
  have hh := numerical_hat_amplitude sign hs hs5
  have he := numerical_exp_sqrt_round_bound hk hK
  have ha : 0 ≤ a := mul_nonneg (mul_nonneg hC0 (Real.exp_pos _).le) hh.1
  have haM : a ≤ sqrtSuzukiAmplitudeCap c k := by
    have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    calc
      _ ≤ (c : ℝ) * (3 : ℝ) ^ (Nat.sqrt k + 1) * 20 := by
        exact mul_le_mul (mul_le_mul hC he (Real.exp_pos _).le hc) hh.2 hh.1 (by positivity)
      _ = _ := by simp only [sqrtSuzukiAmplitudeCap, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]; ring
  have hb := numerical_suzuki_scalar_absorption hD hr (by linarith only [hs]) hs5 ha haM
  convert hb using 1
  dsimp [a, sign, errorEnvelope, Section13HatLayers.kappaHat]
  norm_num only [sub_self, zero_add, Real.rpow_one, Real.rpow_natCast]
  simp only [show s ^ (16 : ℝ) = s ^ (16 : ℕ) by norm_cast]
  ring

def sqrtSuzukiErrorThreshold (c k r : ℕ) : ℕ :=
  3 ^ (5 * max 152587890625 (4096 * (sqrtSuzukiAmplitudeCap c k + 1) ^ 2 * r ^ 2))

theorem numerical_chen_sqrt_suzuki_error {N c k r : ℕ} {C K ε : ℝ}
    (hN : sqrtSuzukiErrorThreshold c k r ≤ N) (hk : 1 ≤ k) (hr : 0 < r)
    (hC0 : 0 ≤ C) (hC : C ≤ c) (hK : K ≤ k) (hε0 : 0 ≤ ε) (hε : ε < 1 / 10)
    (depth : ℕ) :
    C * Real.exp (Real.sqrt K) *
      errorEnvelope jr1965Section13HatLayers depth (chenLevel N ε) 16 (chenS ε) *
      (Real.log (chenLevel N ε)) ^ (-(1 / 2 : ℝ)) < 1 / (r : ℝ) := by
  let H := max 152587890625 (4096 * (sqrtSuzukiAmplitudeCap c k + 1) ^ 2 * r ^ 2)
  have hlogN : ((5 * H : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
    log_ge_power_three (b := 5 * H) hN
  have hNpos : 0 < N := by
    have hh : 0 < sqrtSuzukiErrorThreshold c k r := by unfold sqrtSuzukiErrorThreshold; positivity
    omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hDpos : (0 : ℝ) < chenLevel N ε := by unfold chenLevel; positivity
  have hβ : (2 / 5 : ℝ) ≤ 1 / 2 - ε := by linarith only [hε]
  have hfloor : (N : ℝ) ^ (1 / 2 - ε) ≤ chenLevel N ε :=
    (lt_cast_floor_add_one _).le
  have hlogD : 2 * (H : ℝ) ≤ Real.log (chenLevel N ε) := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hN0 _) hfloor
    rw [Real.log_rpow hN0] at hh
    have hlog0 : 0 ≤ Real.log (N : ℝ) := by
      have hNN : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
      exact Real.log_nonneg hNN
    have hb := mul_le_mul_of_nonneg_right hβ hlog0
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hlogN
    nlinarith only [hh, hb, hlogN]
  have hcut : suzukiScalarThreshold (sqrtSuzukiAmplitudeCap c k) r ≤ chenLevel N ε := by
    have hpow : (0 : ℝ) < (3 : ℝ) ^ H := pow_pos (by norm_num) H
    have hlog3 : Real.log (3 : ℝ) ≤ 2 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    have hp : (3 : ℝ) ^ H ≤ chenLevel N ε := by
      apply (Real.log_le_log_iff hpow hDpos).mp
      rw [Real.log_pow]
      have hh := mul_le_mul_of_nonneg_left hlog3 (Nat.cast_nonneg H)
      nlinarith only [hh, hlogD]
    exact_mod_cast hp
  apply numerical_sqrt_suzuki_error_at_level hcut hk hr hC0 hC hK _ _ depth
  · unfold chenS
    linarith only [hε]
  · unfold chenS
    linarith only [hε0]


#print axioms numerical_chen_sqrt_suzuki_error
end ChenEffective
