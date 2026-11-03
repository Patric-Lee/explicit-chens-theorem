import NumericalSuzukiNormalization
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145OddLowStripSmallLogActual

namespace ChenEffective
open Real MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

noncomputable def lowStripNumericalConstant (C1 : ℝ) : ℝ :=
  9000 * C1 ^ (6 : ℕ) * (Nat.factorial 88 : ℝ)

theorem numerical_small_power {L a : ℝ} (hL : 1 / 2 ≤ L) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    L ^ a ≤ 3 * L := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  by_cases hh : L ≤ 1
  · have hp := Real.rpow_le_one hL0 hh ha
    linarith only [hp, hL]
  · have hp := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hh) ha1
    rw [Real.rpow_one] at hp
    linarith only [hp, hL]

/-- A finite polynomial bound replacing the low-strip eventual-K witness. -/
theorem numerical_low_strip_scalar {C1 K : ℝ} {D : ℕ}
    (_hC1 : 0 ≤ C1) (hK : 2 ≤ K) (hD : 2 ≤ D)
    (hsmall : Real.log (D : ℝ) ≤ C1 * K ^ (7 : ℝ)) :
    let L := Real.log (D : ℝ)
    let R := (L / Real.log 2) * (1 + K / Real.log 2)
    2 * R ^ (2 : ℕ) * L * sourceSigma (D : ℝ) 16 * L ^ (1 / 2 : ℝ) ≤
      lowStripNumericalConstant C1 * Real.exp (Real.sqrt K) := by
  let L := Real.log (D : ℝ)
  let R := (L / Real.log 2) * (1 + K / Real.log 2)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hLhalf : (1 / 2 : ℝ) ≤ L := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ D by exact_mod_cast hD)
    dsimp [L]
    linarith only [hh, Real.log_two_gt_d9]
  have hL0 : 0 < L := by linarith only [hLhalf]
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hloghalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hlog0 : 0 < Real.log 2 := by linarith only [hloghalf]
  have hdivL : L / Real.log 2 ≤ 2 * L := by
    apply (div_le_iff₀ hlog0).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hloghalf hL0.le]
  have hdivK : K / Real.log 2 ≤ 2 * K := by
    apply (div_le_iff₀ hlog0).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hloghalf hK0]
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR : R ≤ 6 * L * K := by
    have hh := mul_le_mul hdivL (show 1 + K / Real.log 2 ≤ 3 * K by linarith only [hdivK, hK])
      (by positivity) (show 0 ≤ 2 * L by positivity)
    dsimp [R]
    nlinarith only [hh]
  have hlog27 : Real.log 27 ≤ (6 : ℝ) := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith only [hh]
  have hinner0 : 0 < Real.log (27 * (D : ℝ)) :=
    Real.log_pos (by nlinarith only [show (2 : ℝ) ≤ D by exact_mod_cast hD])
  have hll : Real.log (Real.log (27 * (D : ℝ))) ≤ 13 * L := by
    have hh := Real.log_le_sub_one_of_pos hinner0
    rw [Real.log_mul (by norm_num) hD0.ne'] at hh
    change Real.log (Real.log (27 * (D : ℝ))) ≤ _
    rw [Real.log_mul (by norm_num) hD0.ne']
    dsimp [L] at hLhalf ⊢
    linarith only [hh, hlog27, hLhalf]
  have hll0 : 0 ≤ Real.log (Real.log (27 * (D : ℝ))) := by
    have hh : (1 : ℝ) ≤ Real.log (27 * (D : ℝ)) := by
      have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
        (show (3 : ℝ) ≤ 27 * D by nlinarith only [show (2 : ℝ) ≤ D by exact_mod_cast hD])
      exact one_le_log_three.trans hh
    exact Real.log_nonneg hh
  have hsigma : sourceSigma (D : ℝ) 16 ≤ 39 * L ^ (2 : ℕ) := by
    have hh := mul_le_mul (numerical_small_power hLhalf (by norm_num : (0 : ℝ) ≤ 1 / 16) (by norm_num)) hll
      hll0 (show 0 ≤ 3 * L by positivity)
    change L ^ (1 / 16 : ℝ) * Real.log (Real.log (27 * (D : ℝ))) ≤ _
    nlinarith only [hh]
  have hsigma0 : 0 ≤ sourceSigma (D : ℝ) 16 := (sourceSigma_pos_of_nat_two_le hD).le
  have hhalf := numerical_small_power hLhalf (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hR2 : R ^ (2 : ℕ) ≤ (6 * L * K) ^ (2 : ℕ) := pow_le_pow_left₀ hR0 hR 2
  have hraw : 2 * R ^ (2 : ℕ) * L * sourceSigma (D : ℝ) 16 * L ^ (1 / 2 : ℝ) ≤
      9000 * L ^ (6 : ℕ) * K ^ (2 : ℕ) := by
    calc
      _ ≤ 2 * (6 * L * K) ^ (2 : ℕ) * L * (39 * L ^ (2 : ℕ)) * (3 * L) := by
        gcongr
      _ ≤ _ := by nlinarith only [mul_nonneg (pow_nonneg hL0.le 6) (sq_nonneg K)]
  have hp : L ^ (6 : ℕ) * K ^ (2 : ℕ) ≤ C1 ^ (6 : ℕ) * K ^ (44 : ℕ) := by
    have hsmall' : L ≤ C1 * K ^ (7 : ℕ) := by
      rw [← Real.rpow_natCast]
      exact hsmall
    have hh := pow_le_pow_left₀ hL0.le hsmall' 6
    have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg K)
    calc
      _ ≤ (C1 * K ^ (7 : ℕ)) ^ (6 : ℕ) * K ^ (2 : ℕ) := hh'
      _ = _ := by ring
  have hseries := Real.pow_div_factorial_le_exp (Real.sqrt K) (Real.sqrt_nonneg K) 88
  have hfac : (0 : ℝ) < Nat.factorial 88 := by exact_mod_cast Nat.factorial_pos 88
  have hKpow : K ^ (44 : ℕ) ≤ (Nat.factorial 88 : ℝ) * Real.exp (Real.sqrt K) := by
    have hh := (div_le_iff₀ hfac).mp hseries
    have heq : (Real.sqrt K) ^ (88 : ℕ) = K ^ (44 : ℕ) := by
      rw [show (88 : ℕ) = 2 * 44 by norm_num, pow_mul, Real.sq_sqrt hK0]
    rw [heq] at hh
    nlinarith only [hh]
  dsimp only
  change 2 * R ^ (2 : ℕ) * L * sourceSigma (D : ℝ) 16 * L ^ (1 / 2 : ℝ) ≤ _
  calc
    _ ≤ 9000 * L ^ (6 : ℕ) * K ^ (2 : ℕ) := hraw
    _ ≤ 9000 * C1 ^ (6 : ℕ) * K ^ (44 : ℕ) := by nlinarith only [hp]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hKpow (show 0 ≤ 9000 * C1 ^ (6 : ℕ) by positivity)
      dsimp [lowStripNumericalConstant]
      nlinarith only [hh]

theorem numerical_low_strip_actual
    (S : BoundingSieve) (H : Section13HatLayers) (hH : Section13HatContract H 2)
    {N D : ℕ} {C1 K s : ℝ} (hC1 : 0 ≤ C1) (hK : 2 ≤ K) (hD : 2 ≤ D)
    (hN : Odd N) (hlocal : HasDimensionOneLocalProductBound S K) (hs1 : 1 < s) (hs2 : s ≤ 2)
    (hsmall : Real.log (D : ℝ) ≤ C1 * K ^ (7 : ℝ)) :
    ActualClaim145BoundAt S H N D 16 (1 / 2) K s (lowStripNumericalConstant C1) := by
  exact claim145_odd_lowStrip_pointwise_of_scalar S H hH hN hlocal
    (by linarith only [hK]) (by unfold lowStripNumericalConstant; positivity) hD hs1 hs2
    (numerical_low_strip_scalar hC1 hK hD hsmall)

#print axioms numerical_low_strip_scalar
#print axioms numerical_low_strip_actual
end ChenEffective
