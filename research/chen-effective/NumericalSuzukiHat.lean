import NumericalSuzukiAbsorption
import MathlibNt.SieveTheory.LinearSieve.JurkatRichert.JurkatRichert1965Section13HatSource

namespace ChenEffective
open Real
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem numerical_hat_bound (sign : ErrorSign) {s : ℝ} (hs : 2 ≤ s) :
    0 ≤ jr1965Section13HatLayers.T sign s ∧ jr1965Section13HatLayers.T sign s ≤ 4 := by
  have hpos := jr1965Section13HatSourceContract.positive sign s (by linarith only [hs])
  have hb : |jr1965Section13HatLayers.T sign s| ≤
      (Real.exp 2 * (1 + Real.exp 1)) * Real.exp (-s) := by
    cases sign
    · exact abs_jr1965HatPlus_le_exp hs
    · exact abs_jr1965HatMinus_le_exp hs
  refine ⟨hpos.le, ?_⟩
  calc
    _ ≤ |jr1965Section13HatLayers.T sign s| := le_abs_self _
    _ ≤ _ := hb
    _ = (1 + Real.exp 1) * Real.exp (2 - s) := by rw [Real.exp_sub, Real.exp_neg]; ring
    _ ≤ (1 + Real.exp 1) * 1 := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith only [hs]))
      positivity
    _ ≤ 4 := by linarith [Real.exp_one_lt_d9]

theorem numerical_hat_amplitude (sign : ErrorSign) {s : ℝ} (hs : 2 ≤ s) (hs5 : s ≤ 5) :
    0 ≤ s * jr1965Section13HatLayers.T sign s ∧
      s * jr1965Section13HatLayers.T sign s ≤ 20 := by
  have hh := numerical_hat_bound sign hs
  refine ⟨mul_nonneg (by linarith only [hs]) hh.1, ?_⟩
  exact (mul_le_mul hs5 hh.2 hh.1 (by norm_num : (0 : ℝ) ≤ 5)).trans_eq (by norm_num)

theorem numerical_exp_sqrt_bound {K : ℝ} {k : ℕ} (hk : 1 ≤ k) (hK : K ≤ k) :
    Real.exp (Real.sqrt K) ≤ (3 : ℝ) ^ k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs : Real.sqrt K ≤ (k : ℝ) :=
    (Real.sqrt_le_sqrt hK).trans (Real.sqrt_le_self_iff.mpr (Or.inr hkR))
  calc
    _ ≤ Real.exp (k : ℝ) := Real.exp_le_exp.mpr hs
    _ = Real.exp 1 ^ k := by rw [← Real.exp_nat_mul, mul_one]
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos 1).le
      (Real.exp_one_lt_d9.le.trans (by norm_num)) k

def suzukiAmplitudeCap (c k : ℕ) : ℕ := 20 * c * 3 ^ k

theorem numerical_suzuki_error_at_level {D c k r : ℕ} {C K s : ℝ}
    (hD : suzukiScalarThreshold (suzukiAmplitudeCap c k) r ≤ D)
    (hk : 1 ≤ k) (hr : 0 < r) (hC0 : 0 ≤ C) (hC : C ≤ c) (hK : K ≤ k)
    (hs : 2 ≤ s) (hs5 : s ≤ 5) (depth : ℕ) :
    C * Real.exp (Real.sqrt K) * errorEnvelope jr1965Section13HatLayers depth D 16 s *
      (Real.log D) ^ (-(1 / 2 : ℝ)) < 1 / (r : ℝ) := by
  let sign := ErrorSign.ofDepth depth
  let a := C * Real.exp (Real.sqrt K) * (s * jr1965Section13HatLayers.T sign s)
  have hh := numerical_hat_amplitude sign hs hs5
  have he := numerical_exp_sqrt_bound hk hK
  have ha : 0 ≤ a := mul_nonneg (mul_nonneg hC0 (Real.exp_pos _).le) hh.1
  have haM : a ≤ suzukiAmplitudeCap c k := by
    have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    calc
      _ ≤ (c : ℝ) * (3 : ℝ) ^ k * 20 := by
        exact mul_le_mul (mul_le_mul hC he (Real.exp_pos _).le hc) hh.2 hh.1 (by positivity)
      _ = _ := by simp only [suzukiAmplitudeCap, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]; ring
  have hb := numerical_suzuki_scalar_absorption hD hr (by linarith only [hs]) hs5 ha haM
  convert hb using 1
  dsimp [a, sign, errorEnvelope, Section13HatLayers.kappaHat]
  norm_num only [sub_self, zero_add, Real.rpow_one, Real.rpow_natCast]
  simp only [show s ^ (16 : ℝ) = s ^ (16 : ℕ) by norm_cast]
  ring

def suzukiErrorThreshold (c k r : ℕ) : ℕ :=
  3 ^ (5 * max 152587890625 (4096 * (suzukiAmplitudeCap c k + 1) ^ 2 * r ^ 2))

theorem numerical_chen_suzuki_error {N c k r : ℕ} {C K ε : ℝ}
    (hN : suzukiErrorThreshold c k r ≤ N) (hk : 1 ≤ k) (hr : 0 < r)
    (hC0 : 0 ≤ C) (hC : C ≤ c) (hK : K ≤ k) (hε0 : 0 ≤ ε) (hε : ε < 1 / 10)
    (depth : ℕ) :
    C * Real.exp (Real.sqrt K) *
      errorEnvelope jr1965Section13HatLayers depth (chenLevel N ε) 16 (chenS ε) *
      (Real.log (chenLevel N ε)) ^ (-(1 / 2 : ℝ)) < 1 / (r : ℝ) := by
  let H := max 152587890625 (4096 * (suzukiAmplitudeCap c k + 1) ^ 2 * r ^ 2)
  have hlogN : ((5 * H : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
    log_ge_power_three (b := 5 * H) hN
  have hNpos : 0 < N := by
    have hh : 0 < suzukiErrorThreshold c k r := by unfold suzukiErrorThreshold; positivity
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
  have hcut : suzukiScalarThreshold (suzukiAmplitudeCap c k) r ≤ chenLevel N ε := by
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
  apply numerical_suzuki_error_at_level hcut hk hr hC0 hC hK _ _ depth
  · unfold chenS
    linarith only [hε]
  · unfold chenS
    linarith only [hε0]

#print axioms numerical_hat_amplitude
#print axioms numerical_chen_suzuki_error
end ChenEffective
