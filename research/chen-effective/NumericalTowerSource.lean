import NumericalTowerTools

noncomputable section
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open BridgeAssembly CutoffCorrectedRatio SourceClaim146AssemblyNext
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem tower_source_lower {x : ℝ} (hx : x ≤ (towerU : ℝ)^2) : sourceLowerCutoff x ≤ towerH := by
  have hU1 := towerU_one
  have hmax : max 1 x ≤ (towerU : ℝ)^2 := max_le (by nlinarith only [hU1]) hx
  have hpow : (max 1 x)^(16 : ℝ) ≤ (towerU : ℝ)^32 := by
    rw [show (16 : ℝ)=(16 : ℕ) by norm_num,Real.rpow_natCast]
    have hh := pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) hmax 16
    simpa only [← pow_mul] using hh
  unfold sourceLowerCutoff sourceLowerCutoffFor
  rw [if_neg (by norm_num : (16 : ℝ) ≠ 0)]
  apply exp_U_pow_le_H (n := 32) (by norm_num)
  exact max_le ((Real.exp_one_lt_d9.le.trans (by norm_num : (2.7182818286 : ℝ) ≤ 3)).trans
    ((by norm_num : (3 : ℝ) ≤ 10^100).trans towerU_real_large |>.trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hU1 (show 1 ≤ 32 by norm_num)))) hpow

theorem tower_source_head : sourceRatioHead ≤ towerU := by
  unfold sourceRatioHead sourceLogM
  apply max_le
  · exact (Real.exp_le_exp.mpr (by norm_num : (2309 : ℝ) ≤ 10^12)).trans exp_seed_le_towerU
  · exact (Real.exp_le_exp.mpr (by norm_num)).trans exp_seed_le_towerU

theorem tower_source_log_cutoff : sourceLogCutoff 1 102400 16 ≤ towerH := by
  let rho : ℝ := 1/(16-min (16/2) (1/(4*(2*(16+1)*(1 : ℝ)^2*102400))))-1/16
  have hrho : rho=1/3565158384 := by norm_num [rho]
  have hb0 : 0 < 4/rho := by rw [hrho]; norm_num
  have hb : 4/rho ≤ (3 : ℝ)^40 := by rw [hrho]; norm_num
  have hlog : Real.log (4/rho) ≤ 80 := by
    have hh := Real.log_le_log hb0 hb
    rw [Real.log_pow] at hh
    have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh,h3]
  have he : 0 ≤ 1/(rho/2) := by rw [hrho]; norm_num
  have hecap : 1/(rho/2) ≤ (10^10 : ℝ) := by rw [hrho]; norm_num
  have hpow : (4/rho)^(1/(rho/2)) ≤ Real.exp (10^12 : ℝ) := by
    rw [Real.rpow_def_of_pos hb0]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul hlog hecap he (by norm_num : (0 : ℝ) ≤ 80)
    exact hh.trans (by norm_num)
  have hlog27 : Real.log (27 : ℝ) ≤ towerU :=
    (tower_log_le_self (by norm_num)).trans ((by norm_num : (27 : ℝ) ≤ 10^100).trans towerU_real_large)
  change max (sourceLowerCutoff (sourceLogM 1 102400 16))
    (Real.exp (max 2 (max (Real.log 27) ((4/rho)^(1/(rho/2)))))) ≤ towerH
  apply max_le
  · apply tower_source_lower
    have hM : sourceLogM 1 102400 16 ≤ towerU := by
      unfold sourceLogM
      exact (Real.exp_le_exp.mpr (by norm_num)).trans exp_seed_le_towerU
    exact hM.trans (by nlinarith only [towerU_one])
  · apply exp_U_pow_le_H (n := 1) (by norm_num)
    simpa only [pow_one] using max_le ((by norm_num : (2 : ℝ) ≤ 10^100).trans towerU_real_large)
      (max_le hlog27 (hpow.trans exp_seed_le_towerU))

theorem tower_source_ratio_cutoff : sourceRatioCutoff ≤ towerH := by
  unfold sourceRatioCutoff
  exact max_le tower_source_log_cutoff (tower_source_lower (tower_source_head.trans (by nlinarith only [towerU_one])))

/-- The head comparison has a polynomial reciprocal gap, even at huge M. -/
theorem tower_weighted_head_gaps {M : ℝ} (hM : 4 ≤ M) :
    let a := (1-1/(M+2))^(1/4 : ℝ)
    let R := 1-1/(8*M)
    let q := (R+a)/(2*a)
    let k := (R+a)/(2*R)
    0 < Real.log q ∧ 1/Real.log q ≤ 96*M ∧ 2/(1-k) ≤ 96*M := by
  let b := 1-1/(M+2)
  let a := b^(1/4 : ℝ)
  let R := 1-1/(8*M)
  let q := (R+a)/(2*a)
  let k := (R+a)/(2*R)
  have hM0 : 0 < M := by linarith only [hM]
  have hb1 : b ≤ 1 := by dsimp [b]; exact sub_le_self _ (by positivity)
  have hbhalf : (1/2 : ℝ) ≤ b := by
    have hh : 1/(M+2) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) (by linarith only [hM])
    dsimp [b]
    linarith only [hh]
  have hb0 : 0 < b := lt_of_lt_of_le (by norm_num) hbhalf
  have ha0 : 0 < a := Real.rpow_pos_of_pos hb0 _
  have ha1 : a ≤ 1 := Real.rpow_le_one hb0.le hb1 (by norm_num)
  have haHalf : (1/2 : ℝ) ≤ a := hbhalf.trans (Real.self_le_rpow_of_le_one hb0.le hb1 (by norm_num))
  have ha4 : a^4=b := by
    dsimp [a]
    rw [← Real.rpow_natCast,← Real.rpow_mul hb0.le]
    norm_num
  have ha2 : a^2 ≤ 1 := pow_le_one₀ ha0.le ha1
  have ha3 : a^3 ≤ 1 := pow_le_one₀ ha0.le ha1
  have hh := mul_le_mul_of_nonneg_left (show 1+a+a^2+a^3 ≤ 4 by linarith only [ha1,ha2,ha3]) (sub_nonneg.mpr ha1)
  have hgap : 1/(4*(M+2)) ≤ 1-a := by
    dsimp [b] at ha4
    rw [show (1 : ℝ)/(4*(M+2))=(1/(M+2))/4 by field_simp]
    linarith only [hh,ha4]
  have hInv : 1/(6*M) ≤ 1/(4*(M+2)) := one_div_le_one_div_of_le (by positivity) (by linarith only [hM])
  have hRa : 1/(24*M) ≤ R-a := by
    calc
      _ = 1/(6*M)-1/(8*M) := by field_simp; ring
      _ ≤ (1-a)-1/(8*M) := sub_le_sub_right (hInv.trans hgap) _
      _ = _ := by dsimp [R]; ring
  have hR1 : R ≤ 1 := by dsimp [R]; exact sub_le_self _ (by positivity)
  have hRhalf : (1/2 : ℝ) ≤ R := by
    have hh : 1/(8*M) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) (by linarith only [hM])
    dsimp [R]
    linarith only [hh]
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hRhalf
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq2 : q ≤ 2 := (div_le_iff₀ (by positivity : 0 < 2*a)).mpr (by linarith only [hR1,haHalf])
  have hqGap : 1/(48*M) ≤ q-1 := by
    dsimp [q]
    rw [div_sub_one (by positivity : (2 : ℝ)*a ≠ 0)]
    apply (le_div_iff₀ (by positivity : 0 < 2*a)).mpr
    have hh := mul_le_mul_of_nonneg_left ha1 (show 0 ≤ 1/(24*M) by positivity)
    have heq : 1/(48*M)*(2*a)=a*(1/(24*M)) := by ring
    rw [heq]
    linarith only [hh,hRa]
  have hq1 : 1 < q := by
    have hh : 0 < 1/(48*M) := by positivity
    linarith only [hqGap,hh]
  have hlog0 : 0 < Real.log q := Real.log_pos hq1
  have hlogGap : 1/(96*M) ≤ Real.log q := by
    have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hq0)
    rw [Real.log_inv] at hh
    have hh' : 1-q⁻¹ ≤ Real.log q := by linarith only [hh]
    have heq : 1-q⁻¹ = (q-1)/q := by field_simp
    rw [heq] at hh'
    have h1 : (q-1)/2 ≤ (q-1)/q := div_le_div_of_nonneg_left (by linarith only [hq1]) hq0 hq2
    have h2 := div_le_div_of_nonneg_right hqGap (by norm_num : (0 : ℝ) ≤ 2)
    have heq2 : (1/(48*M))/2=1/(96*M) := by ring
    rw [heq2] at h2
    exact (h2.trans h1).trans hh'
  have hinv : 1/Real.log q ≤ 96*M := by
    apply (div_le_iff₀ hlog0).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < 96*M)).mp hlogGap
    nlinarith only [hh]
  have hkGap : 1/(48*M) ≤ 1-k := by
    dsimp [k]
    rw [one_sub_div (by positivity : (2 : ℝ)*R ≠ 0)]
    apply (le_div_iff₀ (by positivity : 0 < 2*R)).mpr
    have hh := mul_le_mul_of_nonneg_left hR1 (show 0 ≤ 1/(24*M) by positivity)
    have heq : 1/(48*M)*(2*R)=R*(1/(24*M)) := by ring
    rw [heq]
    linarith only [hh,hRa]
  have hk0 : 0 < 1-k := (by positivity : 0 < 1/(48*M)).trans_le hkGap
  have hkInv : 2/(1-k) ≤ 96*M := by
    have hh := (div_le_iff₀ (by positivity : 0 < 48*M)).mp hkGap
    apply (div_le_iff₀ hk0).mpr
    nlinarith only [hh]
  exact ⟨hlog0,hinv,hkInv⟩

#print axioms tower_source_ratio_cutoff
#print axioms tower_weighted_head_gaps
end ChenEffective
