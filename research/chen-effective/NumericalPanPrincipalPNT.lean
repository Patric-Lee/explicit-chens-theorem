import NumericalPanQuotient
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrincipalMoving

namespace ChenEffective
open Real Finset
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.PanPrincipal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

@[irreducible] def panPrimePNTThreshold (s : ℕ) : ℕ :=
  max (numericalBVThreshold s) (logPowerCutoff (highBVExponent s))

theorem numerical_primeCount_li (s t : ℕ) (ht : panPrimePNTThreshold s ≤ t) :
    |primeCount t - liuLogarithmicIntegral (2/Real.log 2) t| ≤
      numericalBVConstant s * (t : ℝ) / Real.log (t : ℝ)^s := by
  have h := ht
  unfold panPrimePNTThreshold at h
  have hbv := numerical_BV s t ((le_max_left _ _).trans h)
  have hcut := (le_max_right _ _).trans h
  have ht9 : 9 ≤ t := (logPowerCutoff_nine_le _).trans hcut
  have hl : 0 < Real.log (t : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < t by omega))
  have hpay := log_pow_le_sqrt_explicit hcut
  have hmod : 1 ≤ panModulusCutoff t (highBVExponent s : ℝ) := by
    unfold panModulusCutoff
    apply Nat.le_floor
    norm_num only [Nat.cast_one, Real.rpow_natCast]
    rw [← Real.sqrt_eq_rpow]
    exact (one_le_div (pow_pos hl _)).mpr hpay
  rw [primeCount_sub_li_eq_standard, ← BombieriVinogradov.standardPrimeAPMaxError_one]
  calc
    _ ≤ BombieriVinogradov.standardPrimeAPPrefixMaxError t 1 :=
      BombieriVinogradov.standardPrimeAPMaxError_le_prefixMaxError t 1
    _ ≤ ∑ q ∈ Icc 1 (panModulusCutoff t (highBVExponent s : ℝ)),
        BombieriVinogradov.standardPrimeAPPrefixMaxError t q :=
      single_le_sum (fun q _ => BombieriVinogradov.standardPrimeAPPrefixMaxError_nonneg t q)
        (mem_Icc.mpr ⟨le_rfl, hmod⟩)
    _ ≤ _ := hbv

@[irreducible] def panRealDivPNTThreshold (s : ℕ) : ℕ :=
  max 2 (max (panPrimePNTThreshold s) (logPowerCutoff s))

theorem numerical_primeCount_li_real_div (s N a : ℕ) (ha : 0 < a)
    (ht : panRealDivPNTThreshold s ≤ N/a) :
    |primeCount (N/a) - liuLogarithmicIntegral (2/Real.log 2) ((N : ℝ)/a)| ≤
      (numericalBVConstant s + 2) * (N/a : ℕ) / Real.log (N/a : ℕ)^s := by
  have hh := ht
  unfold panRealDivPNTThreshold at hh
  have ht2 : 2 ≤ N/a := (le_max_left _ _).trans hh
  have htpnt : panPrimePNTThreshold s ≤ N/a :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hh)
  have htlog : logPowerCutoff s ≤ N/a :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hh)
  have hl : 0 < Real.log (N/a : ℕ) := Real.log_pos (by exact_mod_cast (show 1 < N/a by omega))
  have hpow : Real.log (N/a : ℕ)^s ≤ (N/a : ℕ) :=
    (log_pow_le_sqrt_explicit htlog).trans
      (Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast (show 1 ≤ N/a by omega))))
  have hli := abs_li_real_div_sub_nat_div (2/Real.log 2) ha ht2
  have hlog2 : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have htwo : (1 : ℝ)/Real.log 2 ≤ 2 :=
    (div_le_iff₀ (Real.log_pos (by norm_num))).mpr (by linarith only [hlog2])
  have hcorr : (2 : ℝ) ≤ 2*(N/a : ℕ)/Real.log (N/a : ℕ)^s := by
    apply (le_div_iff₀ (pow_pos hl s)).mpr
    linarith only [hpow]
  calc
    _ ≤ |primeCount (N/a)-liuLogarithmicIntegral (2/Real.log 2) (N/a : ℕ)| +
        |liuLogarithmicIntegral (2/Real.log 2) (N/a : ℕ) -
          liuLogarithmicIntegral (2/Real.log 2) ((N : ℝ)/a)| := abs_sub_le _ _ _
    _ ≤ numericalBVConstant s * (N/a : ℕ)/Real.log (N/a : ℕ)^s + 2 :=
      add_le_add (numerical_primeCount_li s (N/a) htpnt)
        (by rw [abs_sub_comm]; exact hli.trans htwo)
    _ ≤ numericalBVConstant s * (N/a : ℕ)/Real.log (N/a : ℕ)^s +
        2*(N/a : ℕ)/Real.log (N/a : ℕ)^s := add_le_add (le_refl _) hcorr
    _ = _ := by ring

noncomputable def panMovingPNTConstant (s : ℕ) : ℝ := (numericalBVConstant s + 2)*4^s
@[irreducible] def panMovingPNTThreshold (s : ℕ) : ℕ :=
  panQuotientThreshold 0 (panRealDivPNTThreshold s)

theorem numerical_primeCount_li_moving (s N : ℕ) (hN : panMovingPNTThreshold s ≤ N)
    (a : ℕ) (ha : 1 ≤ a) (haN : (a : ℝ) ≤ (N : ℝ)^(2/3 : ℝ)) :
    |primeCount (N/a) - liuLogarithmicIntegral (2/Real.log 2) ((N : ℝ)/a)| ≤
      (panMovingPNTConstant s * (N : ℝ)/Real.log (N : ℝ)^s)/(a : ℝ) := by
  unfold panMovingPNTThreshold at hN
  have hp := numerical_quotient_parameters 0 (panRealDivPNTThreshold s) N hN a ha haN
  have hb := numerical_primeCount_li_real_div s N a (by omega) hp.1
  have hsaving : Real.log (N : ℝ)^s ≤ 4^s*Real.log (N/a : ℕ)^s := by
    simpa only [mul_pow] using pow_le_pow_left₀ hp.2.1.le hp.2.2.2.1 s
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hupper : (N/a : ℕ)*(a : ℝ) ≤ N := by exact_mod_cast Nat.div_mul_le_self N a
  have hJ : 0 ≤ numericalBVConstant s + 2 := by
    unfold numericalBVConstant bvConstant primitiveNumericalConstant principalNumericalConstant
    positivity
  apply hb.trans
  apply (le_div_iff₀ ha0).mpr
  apply (le_div_iff₀ (pow_pos hp.2.1 s)).mpr
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_le_iff₀ (pow_pos hp.2.2.1 s)).mpr
  unfold panMovingPNTConstant
  calc
    _ ≤ (numericalBVConstant s+2)*((N/a : ℕ)*(a : ℝ)) *
        (4^s*Real.log (N/a : ℕ)^s) := by
      have hh := mul_le_mul_of_nonneg_left hsaving
        (show 0 ≤ (numericalBVConstant s+2)*((N/a : ℕ)*(a : ℝ)) by positivity)
      simpa only [mul_assoc] using hh
    _ ≤ (numericalBVConstant s+2)*(N : ℝ)*(4^s*Real.log (N/a : ℕ)^s) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hupper hJ) (by positivity)
    _ = _ := by ring

#print axioms numerical_primeCount_li_moving
end ChenEffective
