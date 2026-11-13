/- Threshold-specialized companion of research/chen-effective/NumericalPanPrimePrefix.lean.
The original producer is retained; all modified numerical statements are rechecked. -/
import BJSH30PanQuotient
import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingLowPrimePrefix

namespace ChenEffective.H30
open Real Complex Finset
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem numerical_global_prime_power {N y : ℕ} (hN : 9 ≤ N) (hy : y ≤ N) :
    globalPrimePowerCorrection y ≤ 4*Real.sqrt N*Real.log N := by
  have hlN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  by_cases hy0 : y=0
  · subst y
    rw [show globalPrimePowerCorrection 0 = 0 by simp [globalPrimePowerCorrection]]
    positivity
  have hy1 : 1 ≤ y := by omega
  have hyR : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have htail := Chebyshev.psi_sub_theta_le (x := (y : ℝ)) (by exact_mod_cast hy1)
  have htwo : (1 : ℝ)/Real.log 2 ≤ 2 :=
    (div_le_iff₀ (Real.log_pos (by norm_num))).mpr (by linarith [Real.log_two_gt_d9])
  calc
    _ ≤ (Chebyshev.psi y-Chebyshev.theta y)/Real.log 2 := globalPrimePowerCorrection_le_psi_sub_theta y
    _ ≤ (2*Real.sqrt y*Real.log y)/Real.log 2 :=
      div_le_div_of_nonneg_right htail (Real.log_nonneg (by norm_num))
    _ ≤ 4*Real.sqrt y*Real.log y := by
      have hh := mul_le_mul_of_nonneg_left htwo
        (show 0 ≤ 2*Real.sqrt y*Real.log y by positivity)
      calc
        _ = (2*Real.sqrt y*Real.log y)*(1/Real.log 2) := by ring
        _ ≤ (2*Real.sqrt y*Real.log y)*2 := hh
        _ = _ := by ring
    _ ≤ _ := mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hy)) (by norm_num))
      (Real.log_le_log hyR (by exact_mod_cast hy)) (Real.log_nonneg (by exact_mod_cast hy1)) (by positivity)

noncomputable def panPrimePrefixConstant (C : ℕ) : ℝ := 3*primitiveNumericalConstant C+4
@[irreducible] def panPrimePrefixThreshold (D : ℕ) : ℕ :=
  max (primitiveNumericalThreshold D) (logPowerCutoff (D+1))

theorem numerical_prime_character_prefix (C D N q : ℕ) (hN : panPrimePrefixThreshold D ≤ N)
    (hq2 : 2 ≤ q) (hq : (q : ℝ) ≤ Real.log (N : ℝ)^C)
    (χ : PrimitiveCharacter q) (hχ : χ.1 ≠ 1) (y : ℕ) (hy : y ≤ N) :
    ‖PanLow.primePrefix χ.1 y‖ ≤ panPrimePrefixConstant C*N/Real.log (N : ℝ)^D := by
  have hn := hN
  unfold panPrimePrefixThreshold at hn
  have hprim := (le_max_left _ _).trans hn
  have hlogcut := (le_max_right _ _).trans hn
  have hN9 : 9 ≤ N := (logPowerCutoff_nine_le _).trans hlogcut
  let : NeZero q := ⟨by omega⟩
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hK : 0 ≤ primitiveNumericalConstant C := by unfold primitiveNumericalConstant; positivity
  have hab : ‖∑ n ∈ range (y+1), (reciprocalLogWeight n : ℂ)*
      (lambdaNatCoeff n*χ.1 (n : ZMod q))‖ ≤
        3*(primitiveNumericalConstant C*N/Real.log (N : ℝ)^D) := by
    apply (PanLow.norm_abel_le _ y _ (by
      intro n hn
      exact numerical_low_prefix hprim hq χ.1 hχ n (hn.trans hy))).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact (show discreteAbelAmplifier y ≤ discreteAbelAmplifierPrefixMax y from
      Finset.le_max' _ _ (mem_image.mpr ⟨y, mem_range.mpr (Nat.lt_succ_self y), rfl⟩)).trans
      (discreteAbelAmplifierPrefixMax_le_two_inv_log_two y |>.trans (by
        have hh := Real.log_two_gt_d9
        rw [mul_inv_le_iff₀ (Real.log_pos (by norm_num))]
        linarith only [hh]))
  have hpow := log_pow_le_sqrt_explicit hlogcut
  have hpay : 4*Real.sqrt N*Real.log N ≤ 4*(N : ℝ)/Real.log (N : ℝ)^D := by
    apply (le_div_iff₀ (pow_pos hl D)).mpr
    have hh := mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg (N : ℝ))
    rw [Real.mul_self_sqrt (Nat.cast_nonneg N)] at hh
    rw [pow_succ] at hh
    nlinarith only [hh]
  rw [PanLow.primePrefix_eq_abel_sub_correction]
  exact ((norm_sub_le _ _).trans (add_le_add hab
    ((PanLow.norm_correction_le χ.1 y).trans ((numerical_global_prime_power hN9 hy).trans hpay)))).trans_eq
      (by unfold panPrimePrefixConstant; ring)

noncomputable def panMovingPrimeConstant (b s : ℕ) : ℝ := panPrimePrefixConstant (b+2)*4^s
@[irreducible] def panMovingPrimeThreshold (b s : ℕ) : ℕ :=
  panQuotientThreshold b (panPrimePrefixThreshold s)

theorem numerical_prime_character_moving (b s N : ℕ) (hN : panMovingPrimeThreshold b s ≤ N)
    (a : ℕ) (ha : 1 ≤ a) (haN : (a : ℝ) ≤ (N : ℝ)^(2/3 : ℝ))
    (q : ℕ) (hq2 : 2 ≤ q) (hq : (q : ℝ) ≤ Real.log (N : ℝ)^b)
    (χ : PrimitiveCharacter q) (hχ : χ.1 ≠ 1) :
    ‖PanLow.primePrefix χ.1 (N/a)‖ ≤
      (panMovingPrimeConstant b s*N/Real.log (N : ℝ)^s)/(a : ℝ) := by
  unfold panMovingPrimeThreshold at hN
  have hp := numerical_quotient_parameters b (panPrimePrefixThreshold s) N hN a ha haN
  have hcond : Real.log (N : ℝ)^b ≤ Real.log (N/a : ℕ)^(b+2) := by
    calc
      _ ≤ (4*Real.log (N/a : ℕ))^b := pow_le_pow_left₀ hp.2.1.le hp.2.2.2.1 b
      _ = 4^b*Real.log (N/a : ℕ)^b := mul_pow _ _ _
      _ ≤ Real.log (N/a : ℕ)^2*Real.log (N/a : ℕ)^b :=
        mul_le_mul_of_nonneg_right hp.2.2.2.2 (pow_nonneg hp.2.2.1.le b)
      _ = _ := by rw [pow_add]; ring
  have hb := numerical_prime_character_prefix (b+2) s (N/a) q hp.1 hq2
    (hq.trans hcond) χ hχ (N/a) le_rfl
  have hsaving : Real.log (N : ℝ)^s ≤ 4^s*Real.log (N/a : ℕ)^s := by
    simpa only [mul_pow] using pow_le_pow_left₀ hp.2.1.le hp.2.2.2.1 s
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hupper : (N/a : ℕ)*(a : ℝ) ≤ N := by exact_mod_cast Nat.div_mul_le_self N a
  have hJ : 0 ≤ panPrimePrefixConstant (b+2) := by
    unfold panPrimePrefixConstant primitiveNumericalConstant; positivity
  apply hb.trans
  apply (le_div_iff₀ ha0).mpr
  apply (le_div_iff₀ (pow_pos hp.2.1 s)).mpr
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_le_iff₀ (pow_pos hp.2.2.1 s)).mpr
  unfold panMovingPrimeConstant
  calc
    _ ≤ panPrimePrefixConstant (b+2)*((N/a : ℕ)*(a : ℝ)) *
        (4^s*Real.log (N/a : ℕ)^s) := by
      have hh := mul_le_mul_of_nonneg_left hsaving
        (show 0 ≤ panPrimePrefixConstant (b+2)*((N/a : ℕ)*(a : ℝ)) by positivity)
      simpa only [mul_assoc] using hh
    _ ≤ panPrimePrefixConstant (b+2)*(N : ℝ)*(4^s*Real.log (N/a : ℕ)^s) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hupper hJ) (by positivity)
    _ = _ := by ring

#print axioms numerical_prime_character_moving
end ChenEffective.H30
