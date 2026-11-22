import GRHSub13CompleteAnalytic
import Lean.Util.CollectAxioms

/-! Strong GRH estimates for moving prime-character and principal sums.
The low-conductor lane is paid for log N >= 10000, independently of the
current Chen cutoff. The previously checked Chen release is unchanged. -/
noncomputable section
namespace ChenEffective.GRHStrongMoving
open Real Finset
open MathlibNt.SieveTheory LiuWeight
open AnalyticNumberTheory.LargeSieve
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem log_cap {L : ℝ} (hL : 10000≤ L) : log L≤ L/1000 := by
  have hl : 0<L := by linarith only [hL]
  have he := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤27/10)
    (by linarith only [exp_one_gt_d9] : (27/10:ℝ)≤ exp 1) 10
  rw [← exp_nat_mul] at he
  norm_num only [Nat.cast_ofNat,mul_one] at he
  have hlog : log (10000:ℝ)≤10 := by
    have hx : (10000:ℝ)≤ exp 10 := by norm_num at he; linarith only [he]
    have hh := log_le_log (by norm_num : (0:ℝ)<10000) hx
    rwa [log_exp] at hh
  have hh := log_le_sub_one_of_pos (show 0<L/10000 by positivity)
  rw [log_div hl.ne' (by norm_num : (10000:ℝ)≠0)] at hh
  linarith only [hh,hlog,hL]

theorem polynomial_payment {L A α : ℝ} {k : ℕ}
    (hL : (10000:ℝ)≤ L) (hA : A≤(1e20:ℝ))
    (hα : (1497/10000:ℝ)≤α) (hk : k≤80) :
    A*L^k*exp (-α*L)≤1 := by
  have hl : 0<L := by linarith only [hL]
  have he := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤27/10)
    (by linarith only [exp_one_gt_d9] : (27/10:ℝ)≤ exp 1) 50
  rw [← exp_nat_mul] at he
  norm_num only [Nat.cast_ofNat,mul_one] at he
  have hc : (1e20:ℝ)≤ exp 50 := by norm_num at he; linarith only [he]
  have hp : L^k≤ exp (80*L/1000) := by
    calc
      _ ≤ L^80 := pow_le_pow_right₀ (by linarith only [hL] : (1:ℝ)≤ L) hk
      _ = exp (80*log L) := by
        have he := exp_nat_mul (log L) 80
        norm_num only [Nat.cast_ofNat] at he
        rw [exp_log hl] at he
        exact he.symm
      _ ≤ _ := exp_le_exp.mpr (by linarith only [log_cap hL])
  calc
    _ ≤ exp 50*exp (80*L/1000)*exp (-α*L) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul (hA.trans hc) hp
        (pow_nonneg hl.le _) (exp_pos _).le) (exp_pos _).le
    _ = exp (50+80*L/1000-α*L) := by rw [← exp_add,← exp_add]; congr 1; ring
    _ ≤ 1 := by
      rw [← exp_zero]
      apply exp_le_exp.mpr
      nlinarith only [hL,mul_nonneg hl.le (sub_nonneg.mpr hα)]

theorem nine_of_log {N : ℕ} (hL : (10000:ℝ)≤ log (N:ℝ)) : 9≤ N := by
  have hn : 0<N := by
    by_contra h
    have hz : N=0 := by omega
    subst N
    norm_num at hL
  have hh := log_le_sub_one_of_pos (show (0:ℝ)<N by exact_mod_cast hn)
  exact_mod_cast (by linarith only [hL,hh] : (9:ℝ)≤ N)

theorem character_prefix_through {t y q : ℕ} [NeZero q]
    (ht : 9≤ t) (hL : (10:ℝ)≤ log (t:ℝ)) (hy : y≤ t)
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) :
    ‖lambdaCharacterPrefix y q χ‖≤
      (1e14:ℝ)*(log (q:ℝ)+log (t:ℝ))^2*(t:ℝ)^(501/1000:ℝ) := by
  have ht1 : (1:ℝ)≤ t := by exact_mod_cast (show 1≤ t by omega)
  have hq1 : (1:ℝ)≤ q := by exact_mod_cast NeZero.pos q
  have hlq : 0≤ log (q:ℝ) := log_nonneg hq1
  have hA : 10≤ log (q:ℝ)+log (t:ℝ) := by linarith only [hlq,hL]
  by_cases hly : (10:ℝ)≤ log (y:ℝ)
  · have hypos : (0:ℝ)<y := by
      by_contra h
      have hz : y=0 := by exact_mod_cast (le_antisymm (not_lt.mp h) (Nat.cast_nonneg _))
      subst y
      norm_num at hly
    have hy1 : (1:ℝ)≤ y := by exact_mod_cast (show 1≤ y by exact_mod_cast (Nat.pos_of_ne_zero (by intro h; subst y; norm_num at hly)))
    have hyR : (y:ℝ)≤ t := by exact_mod_cast hy
    have hlog := log_le_log hypos hyR
    have hh := GRH.nonprincipal_prefix_numerical χ hχ hy1 hly
    simp only [Nat.floor_natCast] at hh
    apply hh.trans
    gcongr <;> first | norm_num | linarith only [hlog,hlq,hly]
  · have he10 : exp (10:ℝ)≤59049 := by
      have he := pow_le_pow_left₀ (exp_pos 1).le
        (by linarith only [exp_one_lt_d9] : exp (1:ℝ)≤3) 10
      rw [← exp_nat_mul] at he
      norm_num at he ⊢
      exact he
    have hySmall : (y:ℝ)≤59049 := by
      by_cases hz : y=0
      · subst y; norm_num
      · have hy0 : (0:ℝ)<y := by exact_mod_cast Nat.pos_of_ne_zero hz
        exact (((log_lt_iff_lt_exp hy0).mp (not_le.mp hly)).trans_le he10).le
    have hh := norm_lambdaCharacterPrefix_le_const_mul_self y q χ
    have hc : log (4:ℝ)≤2 := by
      rw [show (4:ℝ)=2^2 by norm_num,log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith only [log_two_lt_d9]
    have hsmall : (log (4:ℝ)+4)*y≤354294 := by
      nlinarith only [hc,hySmall,Nat.cast_nonneg (α:=ℝ) y]
    have hscale : (1:ℝ)≤(log (q:ℝ)+log (t:ℝ))^2*(t:ℝ)^(501/1000:ℝ) :=
      one_le_mul_of_one_le_of_one_le (by nlinarith only [hA]) (one_le_rpow ht1 (by norm_num))
    exact hh.trans (hsmall.trans (by nlinarith only [hscale]))

theorem prime_prefix_numerical {t q : ℕ} [NeZero q]
    (ht : 9≤ t) (hL : (10:ℝ)≤ log (t:ℝ))
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) :
    ‖PanLow.primePrefix χ t‖≤
      (1e15:ℝ)*(log (q:ℝ)+log (t:ℝ))^2*(t:ℝ)^(501/1000:ℝ) := by
  let A := log (q:ℝ)+log (t:ℝ)
  let Y := (t:ℝ)^(501/1000:ℝ)
  have ht1 : (1:ℝ)≤ t := by exact_mod_cast (show 1≤ t by omega)
  have hl : 0≤ log (t:ℝ) := log_nonneg ht1
  have hlq : 0≤ log (q:ℝ) := log_nonneg (by exact_mod_cast NeZero.pos q)
  have hA : 10≤ A := by dsimp [A]; linarith only [hlq,hL]
  have hLA : log (t:ℝ)≤ A := by dsimp [A]; linarith only [hlq]
  have hab : ‖∑ n ∈ range (t+1), (reciprocalLogWeight n:ℂ)*
      (lambdaNatCoeff n*χ (n:ZMod q))‖≤3*((1e14:ℝ)*A^2*Y) := by
    apply (PanLow.norm_abel_le _ t _ (by
      intro n hn
      exact character_prefix_through ht hL hn χ hχ)).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact (show discreteAbelAmplifier t≤ discreteAbelAmplifierPrefixMax t from
      le_max' _ _ (mem_image.mpr ⟨t,mem_range.mpr (Nat.lt_succ_self t),rfl⟩)).trans
      (discreteAbelAmplifierPrefixMax_le_two_inv_log_two t |>.trans (by
        rw [mul_inv_le_iff₀ (log_pos (by norm_num))]
        linarith only [log_two_gt_d9]))
  have hroot : sqrt (t:ℝ)≤ Y := by
    rw [sqrt_eq_rpow]
    exact rpow_le_rpow_of_exponent_le ht1 (by norm_num)
  have hlogA : log (t:ℝ)≤ A^2 := by nlinarith only [hLA,hA]
  have hr := mul_le_mul hroot hlogA hl (by positivity)
  have hp := H30.numerical_global_prime_power ht (le_refl t)
  rw [PanLow.primePrefix_eq_abel_sub_correction]
  have hh := (norm_sub_le _ _).trans (add_le_add hab ((PanLow.norm_correction_le χ t).trans hp))
  change _≤(1e15:ℝ)*A^2*Y
  have hpos : 0≤ A^2*Y := by dsimp only [Y]; positivity
  nlinarith only [hh,hr,hpos]

theorem quotient_of_log {N : ℕ} (hL : (10000:ℝ)≤ log (N:ℝ))
    {a : ℕ} (ha : 1≤ a) (haN : (a:ℝ) ≤ (N:ℝ)^(2/3:ℝ)) :
    (N:ℝ)^(3/10:ℝ) ≤ (N/a:ℕ) ∧
    (10000*3/10:ℝ) ≤ log (N/a:ℕ) ∧ log (N/a:ℕ) ≤ log (N:ℝ) := by
  have hn : 0<N := by
    by_contra h
    have hh : N=0 := by omega
    subst N
    norm_num at hL
  have hnR : (0:ℝ)<N := by exact_mod_cast hn
  have hlarge : 4096≤ N := by
    have hh := log_le_sub_one_of_pos hnR
    exact_mod_cast (by linarith only [hL,hh] : (4096:ℝ)≤ N)
  have ht : (N:ℝ)^(3/10:ℝ)≤(N/a:ℕ) := by
    have ha0 : (0:ℝ)<a := by exact_mod_cast (show 0<a by omega)
    have hN1 : (1:ℝ)≤ N := by exact_mod_cast (show 1≤ N by omega)
    have hG : (2:ℝ)≤(N:ℝ)^(1/30:ℝ) := by
      rw [rpow_def_of_pos hnR]
      have he : (2:ℝ)≤ exp 1 := by linarith only [exp_one_gt_d9]
      exact he.trans (exp_le_exp.mpr (by linarith only [hL]))
    have hquarter : (1:ℝ)≤(N:ℝ)^(3/10:ℝ) := one_le_rpow hN1 (by norm_num)
    have hsplit : (N:ℝ)^(3/10:ℝ)*(N:ℝ)^(1/30:ℝ)=(N:ℝ)^(1/3:ℝ) := by
      rw [← rpow_add hnR]; norm_num
    have hgap : (N:ℝ)^(3/10:ℝ)+1≤(N:ℝ)^(1/3:ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hG (rpow_nonneg hnR.le (3/10:ℝ))
      rw [hsplit] at hh
      linarith only [hh,hquarter]
    have hprod : (N:ℝ)^(1/3:ℝ)*(a:ℝ)≤ N := by
      calc
        _ ≤ (N:ℝ)^(1/3:ℝ)*(N:ℝ)^(2/3:ℝ) := mul_le_mul_of_nonneg_left haN (by positivity)
        _ = _ := by rw [← rpow_add hnR]; norm_num
    have hfloor : (N:ℝ)<(N/a:ℕ)*(a:ℝ)+a := by exact_mod_cast (Nat.lt_div_mul_add (show 0<a by omega) : N<N/a*a+a)
    have hlt : (N:ℝ)^(1/3:ℝ)<(N/a:ℕ)+1 := by nlinarith only [hprod,hfloor,ha0]
    linarith only [hgap,hlt]
  have ht0 : (0:ℝ)<(N/a:ℕ) := (rpow_pos_of_pos hnR _).trans_le ht
  have hh := log_le_log (rpow_pos_of_pos hnR (3/10:ℝ)) ht
  rw [log_rpow hnR] at hh
  refine ⟨ht,by linarith only [hh,hL],?_⟩
  exact log_le_log ht0 (by exact_mod_cast (Nat.div_le_self N a))


theorem moving_power_payment {N a : ℕ} (hL : (10000:ℝ)≤ log (N:ℝ))
    (ha : 1≤ a) (haN : (a:ℝ)≤(N:ℝ)^(2/3:ℝ))
    {A : ℝ} (hA : 0≤ A) (hAcap : A≤(1e20:ℝ))
    {s k : ℕ} (hsk : s+k≤80) :
    A*((N/a:ℕ):ℝ)^(501/1000:ℝ)*Real.log (N:ℝ)^k ≤
      ((N:ℝ)/Real.log (N:ℝ)^s)/(a:ℝ) := by
  obtain ⟨hquart,htL,htU⟩ := quotient_of_log hL ha haN
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
  have htlog : Real.log (N:ℝ)*3/10≤ Real.log (N/a:ℕ) := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hn0 _) hquart
    rw [Real.log_rpow hn0] at hh
    linarith only [hh]
  have hid : ((N/a:ℕ):ℝ)^(501/1000:ℝ)=
      (N/a:ℕ)*Real.exp (-(499/1000:ℝ)*Real.log (N/a:ℕ)) := by
    calc
      _ = Real.exp (Real.log (N/a:ℕ)*(501/1000:ℝ)) := Real.rpow_def_of_pos ht0 _
      _ = Real.exp (Real.log (N/a:ℕ))*Real.exp (-(499/1000:ℝ)*Real.log (N/a:ℕ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ = _ := by rw [Real.exp_log ht0]
  have he : Real.exp (-(499/1000:ℝ)*Real.log (N/a:ℕ)) ≤
      Real.exp (-(1497/10000:ℝ)*Real.log (N:ℝ)) :=
    Real.exp_le_exp.mpr (by linarith only [htlog])
  have hp := polynomial_payment hL hAcap (α:=(1497/10000:ℝ)) le_rfl hsk
  have htbound : A*((N/a:ℕ):ℝ)^(501/1000:ℝ)*Real.log (N:ℝ)^k ≤
      (N/a:ℕ)/Real.log (N:ℝ)^s := by
    apply (le_div_iff₀ (pow_pos hl s)).mpr
    rw [hid]
    have hh := mul_le_mul_of_nonneg_left he
      (show 0≤ A*Real.log (N:ℝ)^(s+k) by positivity)
    have hh' := mul_le_mul_of_nonneg_left (hh.trans hp) (Nat.cast_nonneg (N/a))
    rw [pow_add] at hh'
    nlinarith only [hh']
  apply htbound.trans
  apply (le_div_iff₀ ha0).mpr
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast (Nat.div_mul_le_self N a)) (pow_nonneg hl.le s)

theorem pan_prime_moving {N : ℕ} (hL : (10000:ℝ)≤ log (N:ℝ)) {b s : ℕ}
    (hb : b≤40) (hs : s≤72) (a : ℕ) (ha : 1≤ a)
    (haN : (a:ℝ)≤(N:ℝ)^(2/3:ℝ)) (q : ℕ) (hq2 : 2≤ q)
    (hq : (q:ℝ)≤ log (N:ℝ)^b) (χ : PrimitiveCharacter q) (hχ : χ.1≠1) :
    ‖PanLow.primePrefix χ.1 (N/a)‖≤((N:ℝ)/log (N:ℝ)^s)/(a:ℝ) := by
  let : NeZero q := ⟨by omega⟩
  obtain ⟨ht,htL,htU⟩ := quotient_of_log hL ha haN
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have ht0 : (0:ℝ)<(N/a:ℕ) := by
    by_contra h
    have hz : N/a=0 := by exact_mod_cast (le_antisymm (not_lt.mp h) (Nat.cast_nonneg _))
    rw [hz] at htL
    norm_num at htL
  have ht9 : 9≤ N/a := by
    have hh := log_le_sub_one_of_pos ht0
    exact_mod_cast (by linarith only [hh,htL] : (9:ℝ)≤(N/a:ℕ))
  have hlq : 0≤ log (q:ℝ) := log_nonneg (by exact_mod_cast (show 1≤ q by omega))
  have hlogq := log_le_log (by exact_mod_cast (show 0<q by omega) : (0:ℝ)<q) hq
  rw [log_pow] at hlogq
  have hbR : (b:ℝ)≤40 := by exact_mod_cast hb
  have hc := mul_le_mul_of_nonneg_left (log_cap hL) (Nat.cast_nonneg (α:=ℝ) b)
  have hc' := mul_le_mul_of_nonneg_right hbR (show 0≤ log (N:ℝ)/1000 by positivity)
  have hqL : log (q:ℝ)≤ log (N:ℝ) := by linarith only [hlogq,hc,hc',hl]
  have hAsq : (log (q:ℝ)+log (N/a:ℕ))^2≤(2*log (N:ℝ))^2 :=
    pow_le_pow_left₀ (by linarith only [hlq,htL]) (by linarith only [hqL,htU]) 2
  have hp := prime_prefix_numerical ht9 (by linarith only [htL]) χ.1 hχ
  have hm := mul_le_mul_of_nonneg_right hAsq (show 0≤(1e15:ℝ)*((N/a:ℕ):ℝ)^(501/1000:ℝ) by positivity)
  have hpos : 0≤ log (N:ℝ)^2*((N/a:ℕ):ℝ)^(501/1000:ℝ) := by positivity
  have hmajor : ‖PanLow.primePrefix χ.1 (N/a)‖≤
      (1e17:ℝ)*((N/a:ℕ):ℝ)^(501/1000:ℝ)*log (N:ℝ)^2 := by nlinarith only [hp,hm,hpos]
  exact hmajor.trans (moving_power_payment hL ha haN (by norm_num : (0:ℝ)≤1e17)
    (by norm_num) (s:=s) (k:=2) (by omega))

theorem pan_principal_moving {N : ℕ} (hL : (10000:ℝ)≤ log (N:ℝ)) {s : ℕ}
    (hs : s≤70) (a : ℕ) (ha : 1≤ a) (haN : (a:ℝ)≤(N:ℝ)^(2/3:ℝ)) :
    |PanPrincipal.primeCount (N/a)-liuLogarithmicIntegral (2/Real.log 2) ((N:ℝ)/a)| ≤
      ((N:ℝ)/Real.log (N:ℝ)^s)/(a:ℝ) := by
  obtain ⟨_,htL,htU⟩ := quotient_of_log hL ha haN
  have ht0 : (0:ℝ)<(N/a:ℕ) := by
    by_contra h
    have hh : N/a=0 := by exact_mod_cast (le_antisymm (not_lt.mp h) (Nat.cast_nonneg _))
    rw [hh] at htL
    norm_num at htL
  have ht9 : 9≤ N/a := by
    have hh := Real.log_le_sub_one_of_pos ht0
    exact_mod_cast (by linarith only [htL,hh] : (9:ℝ)≤(N/a:ℕ))
  have ht1 : (1:ℝ)≤(N/a:ℕ) := by exact_mod_cast (show 1≤ N/a by omega)
  have hp := GRH.prime_AP_max_numerical (by omega : 2≤ N/a)
    (by linarith only [htL] : (10:ℝ)≤ Real.log (N/a:ℕ)) (by norm_num : 0<(1:ℕ))
  norm_num only [Nat.cast_one,Real.log_one,zero_add] at hp
  have hpnt : |PanPrincipal.primeCount (N/a)-liuLogarithmicIntegral (2/Real.log 2) (N/a:ℕ)| ≤
      (1e16:ℝ)*Real.log ((N/a:ℕ):ℝ)^3*((N/a:ℕ):ℝ)^(501/1000:ℝ) := by
    rw [PanPrincipal.primeCount_sub_li_eq_standard,
      ← BombieriVinogradov.standardPrimeAPMaxError_one]
    convert (BombieriVinogradov.standardPrimeAPMaxError_le_prefixMaxError (N/a) 1).trans hp using 1 <;> norm_num
  have hreal := PanPrincipal.abs_li_real_div_sub_nat_div (2/Real.log 2)
    (by omega : 0<a) (by omega : 2≤ N/a)
  have htwo : (1:ℝ)/Real.log 2≤2 :=
    (div_le_iff₀ (Real.log_pos (by norm_num))).mpr (by linarith only [Real.log_two_gt_d9])
  have hlog : Real.log ((N/a:ℕ):ℝ)^3≤ Real.log (N:ℝ)^3 :=
    pow_le_pow_left₀ (by linarith only [htL]) htU 3
  have hmajor : (1e16:ℝ)*Real.log ((N/a:ℕ):ℝ)^3*((N/a:ℕ):ℝ)^(501/1000:ℝ) ≤
      (1e16:ℝ)*Real.log (N:ℝ)^3*((N/a:ℕ):ℝ)^(501/1000:ℝ) := by
    gcongr
  have hbudget : 1≤ Real.log (N:ℝ)^3*((N/a:ℕ):ℝ)^(501/1000:ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith only [hL]))
      (Real.one_le_rpow ht1 (by norm_num))
  have hh := abs_sub_le (PanPrincipal.primeCount (N/a))
    (liuLogarithmicIntegral (2/Real.log 2) (N/a:ℕ))
    (liuLogarithmicIntegral (2/Real.log 2) ((N:ℝ)/a))
  have hcap : |PanPrincipal.primeCount (N/a)-liuLogarithmicIntegral (2/Real.log 2) ((N:ℝ)/a)| ≤
      (1e17:ℝ)*((N/a:ℕ):ℝ)^(501/1000:ℝ)*Real.log (N:ℝ)^3 := by
    rw [abs_sub_comm] at hreal
    nlinarith only [hh,hpnt.trans hmajor,hreal.trans htwo,hbudget]
  exact hcap.trans (moving_power_payment hL ha haN
    (by norm_num : (0:ℝ)≤1e17) (by norm_num) (s:=s) (k:=3) (by omega))


theorem low_budget (U b N : ℕ) (hLbig : (10000:ℝ)≤ log (N:ℝ)) (hUb : U+b+1≤80)
    (K : ℝ) (hK : 0 ≤ K) (m A₂ Q : ℕ)
    (hm : 1 ≤ m) (hmN : (m : ℝ) ≤ Real.sqrt N)
    (hA : (A₂ : ℝ) ≤ (N : ℝ)^(2/3 : ℝ))
    (hQ : (Q : ℝ) ≤ Real.log (N : ℝ)^b) :
    (Q : ℝ)*((K*N/Real.log (N : ℝ)^(U+b+2))*(1+Real.log N)+
      (A₂ : ℝ)*(m.primeFactors.card : ℝ)) ≤
        (2*K+2)*N/Real.log (N : ℝ)^U := by
  have hN9 := nine_of_log hLbig
  have hL : 1 ≤ Real.log (N : ℝ) := log_one_le_of_eight_le (by omega)
  have hlog := show log (N:ℝ)^(U+b+1)≤(N:ℝ)^(1/3:ℝ) from by
    have hnR : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
    have hlog := mul_le_mul_of_nonneg_left (log_cap hLbig) (Nat.cast_nonneg (α:=ℝ) (U+b+1))
    have hk : ((U+b+1:ℕ):ℝ)≤80 := by exact_mod_cast hUb
    have hh := mul_le_mul_of_nonneg_right hk (show 0≤ log (N:ℝ)/1000 by positivity)
    rw [rpow_def_of_pos hnR]
    have he := exp_nat_mul (log (log (N:ℝ))) (U+b+1)
    rw [exp_log (by linarith only [hLbig] : 0<log (N:ℝ))] at he
    rw [← he]
    apply exp_le_exp.mpr
    nlinarith only [hlog,hh,hLbig]
  have hlog' : Real.log (N : ℝ)^((U : ℝ)+(b : ℝ)+1) ≤ (N : ℝ)^(1/3 : ℝ) := by
    rw [show (U : ℝ)+(b : ℝ)+1 = ((U+b+1 : ℕ) : ℝ) by push_cast; rfl,
      Real.rpow_natCast]
    exact hlog
  have hmX : (m : ℝ) ≤ N := hmN.trans
    (Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast (show 1 ≤ N by omega))))
  have hcard := PanLow.primeFactors_card_le_log_of_le (by omega : 0 < m) hmX
  have htwo : (Real.log 2)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_iff_one_le_mul₀' (Real.log_pos (by norm_num))]
    linarith [Real.log_two_gt_d9]
  have hW : (m.primeFactors.card : ℝ) ≤ 2*Real.log (N : ℝ) :=
    hcard.trans (mul_le_mul_of_nonneg_right htwo (zero_le_one.trans hL))
  have hh := PanLow.low_budget_scalar
    (show (0 : ℝ) < N by exact_mod_cast (show 0 < N by omega)) hL
    (Nat.cast_nonneg A₂) (Nat.cast_nonneg m.primeFactors.card) (Nat.cast_nonneg Q)
    hK (by norm_num : (0 : ℝ) ≤ 2) hA hW
    (show (Q : ℝ) ≤ Real.log (N : ℝ)^(b : ℝ) by simpa only [Real.rpow_natCast] using hQ) hlog'
  simpa only [show (U : ℝ)+(b : ℝ)+2 = ((U+b+2 : ℕ) : ℝ) by push_cast; rfl,
    Real.rpow_natCast] using hh


theorem pan_low_of_log (U b N : ℕ) (hL : (10000:ℝ)≤ log (N:ℝ))
    (hU : U≤32) (hb : b≤38)
    (m A₁ A₂ Q : ℕ) (g : ℕ→ℂ) (hm : 1≤ m) (hmN : (m:ℝ)≤ Real.sqrt N)
    (hA : (A₂:ℝ)≤(N:ℝ)^(2/3:ℝ)) (hQ : (Q:ℝ)≤ Real.log (N:ℝ)^b)
    (hg : ∀ a∈Ioc A₁ A₂, ‖g a‖≤1) :
    PanLow.nonprincipalLow g (fun n => if n.Prime ∧ n.Coprime m then 1 else 0)
      N A₁ A₂ Q ≤ 4*N/Real.log (N:ℝ)^U := by
  have hN9 := nine_of_log hL
  have hAN : A₂≤ N := by
    exact_mod_cast hA.trans (Real.rpow_le_self_of_one_le
      (by exact_mod_cast (show 1≤ N by omega)) (by norm_num))
  have hp := PanLow.nonprincipalLow_le_prime_budget g N A₁ A₂ Q m 1
    ((U+b+2:ℕ):ℝ) (by omega) hAN (by omega) (by norm_num) hg (by
      intro a ha q hq χ
      obtain ⟨ha₁,ha₂⟩ := mem_Ioc.mp ha
      obtain ⟨hq₂,hqQ⟩ := mem_Icc.mp hq
      simpa only [Real.rpow_natCast,one_mul] using
        pan_prime_moving hL (by omega : b≤40) (by omega : U+b+2≤72)
          a (by omega) ((by exact_mod_cast ha₂ : (a:ℝ)≤ A₂).trans hA)
          q hq₂ ((by exact_mod_cast hqQ : (q:ℝ)≤ Q).trans hQ) χ
          (primitiveCharacter_ne_one_of_two_le hq₂ χ))
  have hh := low_budget U b N hL (by omega) 1 (by norm_num) m A₂ Q hm hmN hA hQ
  simp only [Real.rpow_natCast,one_mul] at hp
  norm_num only [one_mul, mul_one] at hh
  exact hp.trans hh

theorem pan_principal_of_log (s N : ℕ) (hL : (10000:ℝ)≤ log (N:ℝ)) (hs : s≤32)
    (q A₁ A₂ : ℕ) (hq : 1≤ q) (hqN : (q:ℝ)≤ Real.sqrt N)
    (hA : (A₂:ℝ)≤(N:ℝ)^(2/3:ℝ)) :
    |PanPrincipal.principalError N A₁ A₂ q| ≤ 4*N/Real.log (N:ℝ)^s := by
  have hN9 := nine_of_log hL
  have hAN : A₂≤ N := by
    exact_mod_cast hA.trans (Real.rpow_le_self_of_one_le
      (by exact_mod_cast (show 1≤ N by omega)) (by norm_num))
  have hb := PanPrincipal.principalError_le_budget N A₁ A₂ q
    ((N:ℝ)/Real.log (N:ℝ)^(s+2)) (by omega) hAN (by positivity) (by
      intro a ha
      exact pan_principal_moving hL (by omega : s+2≤70) a
        (by have := (mem_Ioc.mp ha).1; omega)
        ((by exact_mod_cast (mem_Ioc.mp ha).2 : (a:ℝ)≤ A₂).trans hA))
  have hp := low_budget s 0 N hL (by omega) 1 (by norm_num)
    q A₂ 1 hq hqN hA (by simp)
  exact hb.trans (by simpa only [Nat.add_zero,Nat.cast_one,one_mul,show (2*1+2:ℝ)=4 by norm_num] using hp)


open ChenEffective.GRHSub13
theorem pan_low_at_target (U b N : ℕ) (hN : targetCutoff≤ N)
    (hU : U≤32) (hb : b≤38)
    (m A₁ A₂ Q : ℕ) (g : ℕ→ℂ) (hm : 1≤ m) (hmN : (m:ℝ)≤ sqrt N)
    (hA : (A₂:ℝ)≤(N:ℝ)^(2/3:ℝ)) (hQ : (Q:ℝ)≤ log (N:ℝ)^b)
    (hg : ∀ a∈Ioc A₁ A₂, ‖g a‖≤1) :
    PanLow.nonprincipalLow g (fun n => if n.Prime ∧ n.Coprime m then 1 else 0)
      N A₁ A₂ Q≤4*N/log (N:ℝ)^U :=
  pan_low_of_log U b N (by linarith only [target_log_lower hN]) hU hb m A₁ A₂ Q g hm hmN hA hQ hg

theorem pan_principal_at_target (s N : ℕ) (hN : targetCutoff≤ N) (hs : s≤32)
    (q A₁ A₂ : ℕ) (hq : 1≤ q) (hqN : (q:ℝ)≤ sqrt N)
    (hA : (A₂:ℝ)≤(N:ℝ)^(2/3:ℝ)) :
    |PanPrincipal.principalError N A₁ A₂ q|≤4*N/log (N:ℝ)^s :=
  pan_principal_of_log s N (by linarith only [target_log_lower hN]) hs q A₁ A₂ hq hqN hA

theorem pan_actual_paid_principal (s N : ℕ) (hN : targetCutoff≤ N) (hs : s≤32)
    (B : ℝ) (q : ℕ) (hq : 1≤ q) (hqN : (q:ℝ)≤ Real.sqrt N) :
    liuPanActualError (2/Real.log 2) N B q ≤
      (liuPanActualNonprincipalMass N (liuPanSourceIntervalLower N B)
        (liuPanSourceIntervalUpper N) q (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))+
        4*N/Real.log (N:ℝ)^s)/q.totient := by
  have hp := pan_principal_at_target s N hN hs q
    (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) hq hqN
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _))
  rw [principalError_eq_liuPanActualPrincipalRaw] at hp
  exact (liuWeight_intervalMaxL_le_nonprincipal_add_principal (2/Real.log 2)
    N (liuSourceZ10 N) (liuSourceY3 N) _ _ q hq).trans
      (div_le_div_of_nonneg_right (add_le_add le_rfl hp) (Nat.cast_nonneg _))

open NumericalPanHigh AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
theorem numerical_pan_ledger (U N : ℕ) (hN : targetCutoff ≤ N) (hU : U≤32)
    (m : ℕ) (hm : m ∈ Icc 1 (panModulusCutoff N ((U+6 : ℕ) : ℝ))) :
    liuPanPrimitiveCofactorLedger N (liuPanSourceIntervalLower N ((U+6 : ℕ) : ℝ))
      (liuPanSourceIntervalUpper N) (panModulusCutoff N ((U+6 : ℕ) : ℝ)) m
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) ≤
        GRHSub13.panLedgerConstant U*N/Real.log (N : ℝ)^U := by
  have hNR : logPowerCutoff (U+2)≤ N := pan_log_cutoff_at_target (by omega) hN
  obtain ⟨hlog, hD1, hD, hDN, hcut⟩ := High.numerical_pan_conductor_bounds (U+6) N hN (by omega)
  have hN9 := (logPowerCutoff_nine_le _).trans hNR
  obtain ⟨hmpos, hmcutoff⟩ := mem_Icc.mp hm
  have hmN : (m : ℝ) ≤ Real.sqrt N :=
    (show (m : ℝ) ≤ panModulusCutoff N ((U+6 : ℕ) : ℝ) by exact_mod_cast hmcutoff).trans hDN
  have hA : (liuPanSourceIntervalUpper N : ℝ) ≤ (N : ℝ)^(2/3 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hAN : liuPanSourceIntervalUpper N ≤ N := by
    exact_mod_cast hA.trans (Real.rpow_le_self_of_one_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num))
  have hf : ∀ a, ‖(liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a : ℂ)‖ ≤ 1 := by
    intro a
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_liuWeight] using
      liuWeight_le_one N (liuSourceZ10 N) (liuSourceY3 N) a
  have hlow := pan_low_at_target U (U+6) N hN hU (by omega) m
    (liuPanSourceIntervalLower N ((U+6 : ℕ) : ℝ)) (liuPanSourceIntervalUpper N)
    ⌊lowConductor N ((U+6 : ℕ) : ℝ)⌋₊
    (panSourceG (fun a => (liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a : ℂ)) m)
    hmpos hmN hA (by
      have hl0 : 0 ≤ Real.log (N : ℝ) := by linarith only [hlog]
      simpa only [lowConductor, Real.rpow_natCast] using
        (Nat.floor_le (Real.rpow_nonneg hl0 ((U+6 : ℕ) : ℝ)))) (by
      intro a _
      unfold panSourceG
      split_ifs
      · exact hf a
      · simp)
  have hhigh := High.numerical_high_source_log_saving (U+6) N hN (by omega) m
    (liuPanSourceIntervalLower N ((U+6 : ℕ) : ℝ)) (liuPanSourceIntervalUpper N)
    (fun a => (liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a : ℂ)) hAN hA
    (log_rpow_lt_liuPanSourceIntervalLower N ((U+6 : ℕ) : ℝ)).le hf
  have he : 6-((U+6 : ℕ) : ℝ) = -(U : ℝ) := by push_cast; ring
  rw [he, Real.rpow_neg (show 0 ≤ Real.log (N : ℝ) by linarith only [hlog]),
    Real.rpow_natCast, ← div_eq_mul_inv] at hhigh
  have hDfun : panSourceD m = (fun n => if n.Prime ∧ n.Coprime m then (1 : ℂ) else 0) := by
    funext n
    simp only [panSourceD, and_comm]
  rw [liuPanPrimitiveCofactorLedger_eq_source,
    PanLow.nonprincipalLow_eq_low_add_high _ _ _ _ _ _ _ hD1 hD,
    panModulusCutoff_eq_upper]
  rw [← hDfun] at hlow
  have hr := H30.numerical_pan_high_remainder U N hNR
  calc
    _ ≤ 4*N/Real.log (N : ℝ)^U +
        (panHighConstant*N/Real.log (N : ℝ)^U + 6984*Real.log (N : ℝ)^2/N) :=
      add_le_add hlow hhigh
    _ ≤ 4*N/Real.log (N : ℝ)^U +
        (panHighConstant*N/Real.log (N : ℝ)^U + 6984*N/Real.log (N : ℝ)^U) := by
      exact add_le_add le_rfl (add_le_add le_rfl hr)
    _ = _ := by unfold GRHSub13.panLedgerConstant; ring


#print axioms character_prefix_through
#print axioms prime_prefix_numerical
#print axioms pan_prime_moving
#print axioms pan_principal_moving
#print axioms pan_low_of_log
#print axioms pan_principal_of_log
#print axioms numerical_pan_ledger
end ChenEffective.GRHStrongMoving
end

open Lean Meta
run_elab do
  if debug.skipKernelTC.get (← getOptions) then throwError "Kernel type checking must be enabled"
  let previous ← getConstInfo ``ChenEffective.GRHSub13.numerical_pan_ledger
  let improved ← getConstInfo ``ChenEffective.GRHStrongMoving.numerical_pan_ledger
  unless (← isDefEq previous.type improved.type) do
    throwError "The strong cofactor ledger changed the production statement"
  logInfo "Strong cofactor ledger has exactly the previous production type."
  let standard := #[``propext,``Classical.choice,``Quot.sound]
  let ax := ``ChenEffective.GRH.alpoge_dirichlet_grh
  let roots := #[``ChenEffective.GRHStrongMoving.character_prefix_through,
    ``ChenEffective.GRHStrongMoving.prime_prefix_numerical,
    ``ChenEffective.GRHStrongMoving.pan_prime_moving,
    ``ChenEffective.GRHStrongMoving.pan_principal_moving,
    ``ChenEffective.GRHStrongMoving.pan_low_of_log,
    ``ChenEffective.GRHStrongMoving.pan_principal_of_log,
    ``ChenEffective.GRHStrongMoving.numerical_pan_ledger,
    ``ChenEffective.GRHStrongMoving.pan_actual_paid_principal]
  let axs ← Lean.collectAxioms ``ChenEffective.GRHStrongMoving.numerical_pan_ledger
  unless axs.contains ax && axs.all (standard.push ax).contains do throwError "Unexpected axiom closure: {axs}"
  let forbidden := #["sorryAx","Lean.ofReduceBool","Lean.trustCompiler",
    "ChenEffective.GRHSub13.pan_prime_moving","ChenEffective.GRHSub13.pan_principal_moving",
    "ChenEffective.GRHSub13.pan_moving_power_payment","ChenEffective.GRHSub13.pan_low_at_target",
    "ChenEffective.GRHSub13.pan_principal_at_target","ChenEffective.GRHSub13.numerical_pan_ledger",
    "ChenEffective.numerical_low_prefix_power"]
  let mut todo := roots
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if forbidden.contains n.toString then throwError "Forbidden or superseded dependency {n}"
    let ci ← getConstInfo n
    if ci.isUnsafe then throwError "Unsafe dependency {n}"
    if ci matches .axiomInfo _ then
      unless (standard.push ax).contains n do throwError "Unlisted axiom {n}"
    todo := todo ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then todo := todo ++ v.getUsedConstants
  logInfo m!"Strong GRH moving audit passed: {seen.size} constants; sole added axiom GRH."
  logInfo "Primitive and principal moving sums and actual low aggregate paid for log N >= 10000."
  logInfo "Actual current-target cofactor ledger uses no superseded weak moving estimate."
