import GRH14PanPayment
import BJSH30PanPrimePrefix
import NumericalPrincipalPNT
import GRHPrimeAPMaxima
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrincipalMoving

noncomputable section
namespace ChenEffective.GRH14
open Real Complex Finset
open MathlibNt.SieveTheory LiuWeight
open AnalyticNumberTheory.LargeSieve
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem pan_prime_prefix_power {t C q : ℕ} [NeZero q]
    (ht : 9≤t) (hC : C≤80) (hq : (q:ℝ)≤Real.log (t:ℝ)^C)
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) :
    ‖PanLow.primePrefix χ t‖ ≤ (1e14:ℝ)*(t:ℝ)^(127/128:ℝ)*Real.log (t:ℝ) := by
  have ht1 : (1:ℝ)≤t := by exact_mod_cast (show 1≤t by omega)
  have hl : 0≤Real.log (t:ℝ) := Real.log_nonneg ht1
  have hab : ‖∑ n ∈ range (t+1), (reciprocalLogWeight n:ℂ)*
      (lambdaNatCoeff n*χ (n:ZMod q))‖ ≤
      3*(primitiveNumericalConstant C*(t:ℝ)^(127/128:ℝ)*Real.log (t:ℝ)) := by
    apply (PanLow.norm_abel_le _ t _ (by
      intro n hn
      exact numerical_low_prefix_power ht hq χ hχ n hn)).trans
    apply mul_le_mul_of_nonneg_right _ (by unfold primitiveNumericalConstant; positivity)
    exact (show discreteAbelAmplifier t ≤ discreteAbelAmplifierPrefixMax t from
      Finset.le_max' _ _ (mem_image.mpr ⟨t,mem_range.mpr (Nat.lt_succ_self t),rfl⟩)).trans
      (discreteAbelAmplifierPrefixMax_le_two_inv_log_two t |>.trans (by
        rw [mul_inv_le_iff₀ (Real.log_pos (by norm_num))]
        linarith only [Real.log_two_gt_d9]))
  have hr : Real.sqrt (t:ℝ) ≤ (t:ℝ)^(127/128:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
  have hp := H30.numerical_global_prime_power ht (le_refl t)
  have hc : 3*primitiveNumericalConstant C+4 ≤ (1e14:ℝ) := by
    unfold primitiveNumericalConstant
    have hh : (C:ℝ)≤80 := by exact_mod_cast hC
    linarith only [hh]
  rw [PanLow.primePrefix_eq_abel_sub_correction]
  have hh := (norm_sub_le _ _).trans (add_le_add hab
    ((PanLow.norm_correction_le χ t).trans hp))
  have hhroot := mul_le_mul_of_nonneg_right hr hl
  have hhcoef := mul_le_mul_of_nonneg_right hc
    (show 0≤(t:ℝ)^(127/128:ℝ)*Real.log (t:ℝ) by positivity)
  nlinarith only [hh,hhroot,hhcoef]

/-- Pay a moving quotient's 1/128 saving before summing over source variables. -/
theorem pan_moving_power_payment {N a : ℕ} (hN : targetCutoff≤N)
    (ha : 1≤a) (haN : (a:ℝ)≤(N:ℝ)^(2/3:ℝ))
    {A : ℝ} (hA : 0≤A) (hAcap : A≤(1e20:ℝ))
    {s k : ℕ} (hsk : s+k≤100) :
    A*((N/a:ℕ):ℝ)^(127/128:ℝ)*Real.log (N:ℝ)^k ≤
      ((N:ℝ)/Real.log (N:ℝ)^s)/(a:ℝ) := by
  obtain ⟨hquart,htL,htU⟩ := pan_quotient_at_target hN ha haN
  have hL := target_log_lower hN
  have hl : 0<Real.log (N:ℝ) := by linarith only [hL]
  have ht0 : (0:ℝ)<(N/a:ℕ) := by
    by_contra h
    have hh : N/a=0 := by exact_mod_cast (le_antisymm (not_lt.mp h) (Nat.cast_nonneg _))
    rw [hh] at htL
    norm_num at htL
  have hn0 : (0:ℝ)<N := by
    have hh : 0<N/a := by exact_mod_cast ht0
    exact_mod_cast (Nat.pos_of_div_pos hh)
  have ha0 : (0:ℝ)<a := by exact_mod_cast (show 0<a by omega)
  have htlog : Real.log (N:ℝ)/4≤Real.log (N/a:ℕ) := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hn0 _) hquart
    rw [Real.log_rpow hn0] at hh
    linarith only [hh]
  have hid : ((N/a:ℕ):ℝ)^(127/128:ℝ)=
      (N/a:ℕ)*Real.exp (-Real.log (N/a:ℕ)/128) := by
    calc
      _ = Real.exp (Real.log (N/a:ℕ)*(127/128:ℝ)) := Real.rpow_def_of_pos ht0 _
      _ = Real.exp (Real.log (N/a:ℕ))*Real.exp (-Real.log (N/a:ℕ)/128) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ = _ := by rw [Real.exp_log ht0]
  have he : Real.exp (-Real.log (N/a:ℕ)/128) ≤
      Real.exp (-(1/512:ℝ)*Real.log (N:ℝ)) :=
    Real.exp_le_exp.mpr (by linarith only [htlog])
  have hp := pan_polynomial_payment hL hAcap (α:=(1/512:ℝ)) le_rfl hsk
  have htbound : A*((N/a:ℕ):ℝ)^(127/128:ℝ)*Real.log (N:ℝ)^k ≤
      (N/a:ℕ)/Real.log (N:ℝ)^s := by
    apply (le_div_iff₀ (pow_pos hl s)).mpr
    rw [hid]
    have hh := mul_le_mul_of_nonneg_left he
      (show 0≤A*Real.log (N:ℝ)^(s+k) by positivity)
    have hh' := mul_le_mul_of_nonneg_left (hh.trans hp) (Nat.cast_nonneg (N/a))
    rw [pow_add] at hh'
    nlinarith only [hh']
  apply htbound.trans
  apply (le_div_iff₀ ha0).mpr
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast (Nat.div_mul_le_self N a)) (pow_nonneg hl.le s)

theorem pan_prime_moving {N : ℕ} (hN : targetCutoff≤N) {b s : ℕ}
    (hb : b≤40) (hs : s≤99) (a : ℕ) (ha : 1≤a)
    (haN : (a:ℝ)≤(N:ℝ)^(2/3:ℝ)) (q : ℕ) (hq2 : 2≤q)
    (hq : (q:ℝ)≤Real.log (N:ℝ)^b) (χ : PrimitiveCharacter q)
    (hχ : χ.1≠1) :
    ‖PanLow.primePrefix χ.1 (N/a)‖ ≤ ((N:ℝ)/Real.log (N:ℝ)^s)/(a:ℝ) := by
  let : NeZero q := ⟨by omega⟩
  obtain ⟨hquart,htL,htU⟩ := pan_quotient_at_target hN ha haN
  have ht0 : (0:ℝ)<(N/a:ℕ) := by
    by_contra h
    have hh : N/a=0 := by exact_mod_cast (le_antisymm (not_lt.mp h) (Nat.cast_nonneg _))
    rw [hh] at htL
    norm_num at htL
  have ht9 : 9≤N/a := by
    have hh := Real.log_le_sub_one_of_pos ht0
    exact_mod_cast (by linarith only [htL,hh] : (9:ℝ)≤(N/a:ℕ))
  have hn0 : (0:ℝ)<N := by exact_mod_cast (Nat.pos_of_div_pos (by omega : 0<N/a))
  have htlog : Real.log (N:ℝ)≤4*Real.log (N/a:ℕ) := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hn0 _) hquart
    rw [Real.log_rpow hn0] at hh
    linarith only [hh]
  have hcond : (q:ℝ)≤Real.log ((N/a:ℕ):ℝ)^(2*b) := by
    apply hq.trans
    calc
      _ ≤ (4*Real.log (N/a:ℕ))^b := pow_le_pow_left₀ (by have := target_log_lower hN; linarith) htlog b
      _ = 4^b*Real.log ((N/a:ℕ):ℝ)^b := mul_pow _ _ _
      _ ≤ Real.log ((N/a:ℕ):ℝ)^b*Real.log ((N/a:ℕ):ℝ)^b := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact pow_le_pow_left₀ (by norm_num) (by linarith only [htL]) b
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hh := pan_prime_prefix_power ht9 (by omega : 2*b≤80) hcond χ.1 hχ
  have hlog := mul_le_mul_of_nonneg_left htU
    (show 0≤(1e14:ℝ)*((N/a:ℕ):ℝ)^(127/128:ℝ) by positivity)
  apply (hh.trans hlog).trans
  simpa only [pow_one] using pan_moving_power_payment hN ha haN
    (A:=(1e14:ℝ)) (by norm_num) (by norm_num) (s:=s) (k:=1) (by omega)

#print axioms pan_prime_moving

theorem pan_principal_moving {N : ℕ} (hN : targetCutoff≤N) {s : ℕ}
    (hs : s≤97) (a : ℕ) (ha : 1≤a) (haN : (a:ℝ)≤(N:ℝ)^(2/3:ℝ)) :
    |PanPrincipal.primeCount (N/a)-liuLogarithmicIntegral (2/Real.log 2) ((N:ℝ)/a)| ≤
      ((N:ℝ)/Real.log (N:ℝ)^s)/(a:ℝ) := by
  obtain ⟨_,htL,htU⟩ := pan_quotient_at_target hN ha haN
  have hL := target_log_lower hN
  have ht0 : (0:ℝ)<(N/a:ℕ) := by
    by_contra h
    have hh : N/a=0 := by exact_mod_cast (le_antisymm (not_lt.mp h) (Nat.cast_nonneg _))
    rw [hh] at htL
    norm_num at htL
  have ht9 : 9≤N/a := by
    have hh := Real.log_le_sub_one_of_pos ht0
    exact_mod_cast (by linarith only [htL,hh] : (9:ℝ)≤(N/a:ℕ))
  have ht1 : (1:ℝ)≤(N/a:ℕ) := by exact_mod_cast (show 1≤N/a by omega)
  have hp := GRH.prime_AP_max_numerical (by omega : 2≤N/a)
    (by linarith only [htL] : (10:ℝ)≤Real.log (N/a:ℕ)) (by norm_num : 0<(1:ℕ))
  norm_num only [Nat.cast_one,Real.log_one,zero_add] at hp
  have hpnt : |PanPrincipal.primeCount (N/a)-liuLogarithmicIntegral (2/Real.log 2) (N/a:ℕ)| ≤
      (1e16:ℝ)*Real.log ((N/a:ℕ):ℝ)^3*((N/a:ℕ):ℝ)^(501/1000:ℝ) := by
    rw [PanPrincipal.primeCount_sub_li_eq_standard,
      ← BombieriVinogradov.standardPrimeAPMaxError_one]
    convert (BombieriVinogradov.standardPrimeAPMaxError_le_prefixMaxError (N/a) 1).trans hp using 1 <;> norm_num
  have hreal := PanPrincipal.abs_li_real_div_sub_nat_div (2/Real.log 2)
    (by omega : 0<a) (by omega : 2≤N/a)
  have htwo : (1:ℝ)/Real.log 2≤2 :=
    (div_le_iff₀ (Real.log_pos (by norm_num))).mpr (by linarith only [Real.log_two_gt_d9])
  have hpow : ((N/a:ℕ):ℝ)^(501/1000:ℝ)≤((N/a:ℕ):ℝ)^(127/128:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
  have hlog : Real.log ((N/a:ℕ):ℝ)^3≤Real.log (N:ℝ)^3 :=
    pow_le_pow_left₀ (by linarith only [htL]) htU 3
  have hmajor : (1e16:ℝ)*Real.log ((N/a:ℕ):ℝ)^3*((N/a:ℕ):ℝ)^(501/1000:ℝ) ≤
      (1e16:ℝ)*Real.log (N:ℝ)^3*((N/a:ℕ):ℝ)^(127/128:ℝ) := by
    gcongr
  have hbudget : 1≤Real.log (N:ℝ)^3*((N/a:ℕ):ℝ)^(127/128:ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith only [hL]))
      (Real.one_le_rpow ht1 (by norm_num))
  have hh := abs_sub_le (PanPrincipal.primeCount (N/a))
    (liuLogarithmicIntegral (2/Real.log 2) (N/a:ℕ))
    (liuLogarithmicIntegral (2/Real.log 2) ((N:ℝ)/a))
  have hcap : |PanPrincipal.primeCount (N/a)-liuLogarithmicIntegral (2/Real.log 2) ((N:ℝ)/a)| ≤
      (1e17:ℝ)*((N/a:ℕ):ℝ)^(127/128:ℝ)*Real.log (N:ℝ)^3 := by
    rw [abs_sub_comm] at hreal
    nlinarith only [hh,hpnt.trans hmajor,hreal.trans htwo,hbudget]
  exact hcap.trans (pan_moving_power_payment hN ha haN
    (by norm_num : (0:ℝ)≤1e17) (by norm_num) (s:=s) (k:=3) (by omega))

#print axioms pan_principal_moving
end ChenEffective.GRH14


