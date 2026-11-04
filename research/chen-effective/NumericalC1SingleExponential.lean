import NumericalTowerC1

noncomputable section
namespace ChenEffective
open Real Set Finset
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

/-- A convenient one-exponential budget for the individual separator terms. -/
def c1SingleBudget : ℝ := Real.exp (10^15 : ℝ)

theorem c1SingleBudget_one : 1 ≤ c1SingleBudget := Real.one_le_exp (by norm_num)

theorem c1_U_pow_budget {n : ℕ} (hn : n ≤ 100) : (towerU : ℝ)^n ≤ c1SingleBudget := by
  have h3 : Real.log (3 : ℝ) ≤ 2 := by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<3)]
  have hu : Real.log (towerU : ℝ) ≤ 2*(10^12 : ℝ) := by
    rw [towerU,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,towerSeed_eq]
    norm_num only [Nat.cast_pow,Nat.cast_ofNat]
    nlinarith only [h3]
  apply (Real.log_le_iff_le_exp (pow_pos towerU_pos n)).mp
  rw [Real.log_pow]
  have hnR : (n : ℝ) ≤ 100 := by exact_mod_cast hn
  have hh := mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg n)
  change (n : ℝ)*Real.log (towerU : ℝ) ≤ (10^15 : ℝ)
  nlinarith only [hh,hnR]

theorem c1_U_budget : (towerU : ℝ) ≤ c1SingleBudget := by
  simpa only [pow_one] using c1_U_pow_budget (show 1 ≤ 100 by norm_num)

theorem c1_log_budget {x : ℝ} (hx : 0 ≤ x) (hbound : x ≤ (towerH : ℝ)^4) :
    c1LogBudget x ≤ c1SingleBudget := by
  apply max_le (zero_le_one.trans c1SingleBudget_one)
  by_cases hx0 : x=0
  · simpa only [hx0,Real.log_zero] using zero_le_one.trans c1SingleBudget_one
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hh : (towerH : ℝ)^4 ≤ (towerH : ℝ)^6 := pow_le_pow_right₀ towerH_one (by norm_num)
  exact (Real.log_le_log hxpos (hbound.trans hh)).trans
    (towerH_log_six_cap.trans (Real.exp_le_exp.mpr (by norm_num)))

theorem c1_caseI_Dcuts : caseIStrictDcut ≤ (towerH : ℝ)^4 ∧ caseIEvenDcut ≤ (towerH : ℝ)^4 := by
  have h14 : (towerH : ℝ) ≤ (towerH : ℝ)^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ towerH_one (show 1 ≤ 4 by norm_num)
  have hu4 := towerU_le_H.trans h14
  have h4 : (4 : ℝ) ≤ (towerH : ℝ)^4 := (by norm_num : (4 : ℝ) ≤ 10^100).trans (towerH_large.trans h14)
  have hr : (recursiveNatCutoff : ℝ) ≤ (towerH : ℝ)^4 := by
    have h : (recursiveNatCutoff : ℝ) ≤ towerU := by exact_mod_cast tower_geometry.2.2
    exact h.trans hu4
  have hq : ((transportQuotientCutoff^2 : ℕ) : ℝ) ≤ (towerH : ℝ)^4 := by
    rw [Nat.cast_pow]
    simpa only [← pow_mul] using pow_le_pow_left₀ (Nat.cast_nonneg _) tower_transport.1 2
  have hf := tower_claim146_cutoff.trans h14
  have hp : preThresholdCutoff ≤ (towerH : ℝ)^4 := max_le (tower_geometry.1.trans hu4) h4
  have he : Real.exp (Real.exp 3) ≤ (towerH : ℝ)^4 :=
    (tower_exp_small (tower_exp_three.trans (by norm_num))).trans hu4
  constructor
  · exact max_le h4 (max_le hf (max_le hf (max_le hp (max_le hr (max_le hq h4)))))
  · exact max_le h4 (max_le hf (max_le hf (max_le hp (max_le he (max_le hr hq)))))

theorem c1_endpoint_budget : (caseIEndpointC1 : ℝ) ≤ c1SingleBudget := by
  have hn : 1200*reverseRatioCap+5 ≤ 10^13 := by norm_num [reverseRatioCap]
  have hnR : ((1200*reverseRatioCap+5 : ℕ) : ℝ) ≤ 10^13 := by exact_mod_cast hn
  have h3 : Real.log (3 : ℝ) ≤ 2 := by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<3)]
  rw [caseIEndpointC1_eq,Nat.cast_pow,Nat.cast_ofNat]
  apply (Real.log_le_iff_le_exp (by positivity)).mp
  rw [Real.log_pow]
  change ((1200*reverseRatioCap+5 : ℕ) : ℝ)*Real.log 3 ≤ (10^15 : ℝ)
  have h := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg (1200*reverseRatioCap+5))
  nlinarith only [h,hnR]

theorem c1_gap_budget : caseIIGapC1 ≤ c1SingleBudget := by
  have hu := c1_U_budget
  have h2 : (2 : ℝ) ≤ c1SingleBudget := (by norm_num : (2 : ℝ) ≤ 10^100).trans (towerU_real_large.trans hu)
  have hsqrt : ((3 : ℝ)/2)^(1/2 : ℝ) ≤ 2 := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 3/2) (by norm_num : (3/2 : ℝ) ≤ 4) (by norm_num : (0 : ℝ) ≤ 1/2)
    norm_num at h ⊢
    exact h
  have hM : caseIIGapAmplitude ≤ 10^12 := by
    unfold caseIIGapAmplitude
    norm_num only [Real.rpow_ofNat,Nat.reducePow]
    linarith only [hsqrt]
  have hbase : max 1 (128*caseIIGapAmplitude/(5*(1-(1/2 : ℝ)))) ≤ (10^14 : ℝ) := by
    apply max_le (by norm_num)
    norm_num
    linarith only [hM]
  have hp10 : (10 : ℝ)^560 ≤ c1SingleBudget := by
    apply (Real.log_le_iff_le_exp (by positivity)).mp
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have h10 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<10)
    linarith only [h10]
  have hpow : (max 1 (128*caseIIGapAmplitude/(5*(1-(1/2 : ℝ)))) )^
      (1/((1-(1/2 : ℝ))-(2/7+3/16))) ≤ c1SingleBudget := by
    calc
      _ ≤ (10^14 : ℝ)^(1/((1-(1/2 : ℝ))-(2/7+3/16))) :=
        Real.rpow_le_rpow (zero_le_one.trans (le_max_left _ _)) hbase (by norm_num)
      _ ≤ (10^14 : ℝ)^40 := tower_rpow_le_nat (by norm_num) (by norm_num)
      _ = (10 : ℝ)^560 := by rw [← pow_mul]
      _ ≤ _ := hp10
  have hcut : (coreDecayLogCutoff : ℝ) ≤ c1SingleBudget := by
    have h : coreDecayLogCutoff ≤ towerU := by
      unfold coreDecayLogCutoff logPowerCutoff towerU
      apply Nat.pow_le_pow_right (by norm_num)
      rw [towerSeed_eq]
      norm_num
    exact (show (coreDecayLogCutoff : ℝ) ≤ towerU by exact_mod_cast h).trans hu
  have hcore : coreDecayCutoff caseIIGapAmplitude ≤ c1SingleBudget := by
    unfold coreDecayCutoff
    exact max_le (max_le h2 (tower_log27.trans hu)) (max_le hcut hpow)
  unfold caseIIGapC1
  exact max_le hcore (max_le ((tower_exp_small (by norm_num)).trans hu)
    ((by norm_num : (3 : ℝ)^(16 : ℝ) ≤ 10^100).trans (towerU_real_large.trans hu)))

/-- The complete Suzuki separator now has a single-exponential numerical cap. -/
theorem numericalSuzukiC1_single_exp_sharp_cap : numericalSuzukiC1 ≤ Real.exp (10^16 : ℝ) := by
  have hP1 := c1SingleBudget_one
  have hP0 := zero_le_one.trans hP1
  have h14 : (towerH : ℝ) ≤ (towerH : ℝ)^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ towerH_one (show 1 ≤ 4 by norm_num)
  have hu4 := towerU_le_H.trans h14
  have h4 : (4 : ℝ) ≤ (towerH : ℝ)^4 := (by norm_num : (4 : ℝ) ≤ 10^100).trans (towerH_large.trans h14)
  have hr : (recursiveNatCutoff : ℝ) ≤ (towerH : ℝ)^4 := by
    have h : (recursiveNatCutoff : ℝ) ≤ towerU := by exact_mod_cast tower_geometry.2.2
    exact h.trans hu4
  have hb : caseBSourceC1 ≤ c1SingleBudget := by
    rw [caseBSourceC1_eq]
    exact Real.exp_le_exp.mpr (by norm_num)
  have hscalar : (caseIScalarC1 : ℝ) ≤ c1SingleBudget := tower_endpoint_caps.2.trans c1_U_budget
  have hsigma : sigmaZeroC1 ≤ c1SingleBudget := by
    unfold sigmaZeroC1
    rw [Real.log_exp]
    exact max_le hb (Real.exp_le_exp.mpr (by norm_num))
  have hstrict : caseIStrictC1 ≤ c1SingleBudget := by
    have hl := c1_log_budget (x := caseIStrictDcut)
      ((by norm_num : (0 : ℝ) ≤ 4).trans (le_max_left _ _)) c1_caseI_Dcuts.1
    unfold caseIStrictC1
    exact max_le hP1 (max_le c1_endpoint_budget (max_le hscalar (max_le hsigma
      (max_le hP1 ((le_max_right _ _).trans hl)))))
  have heven : caseIEvenC1 ≤ c1SingleBudget := by
    have hl := c1_log_budget (x := caseIEvenDcut)
      ((by norm_num : (0 : ℝ) ≤ 4).trans (le_max_left _ _)) c1_caseI_Dcuts.2
    unfold caseIEvenC1
    exact max_le hP1 (max_le c1_endpoint_budget (max_le hscalar (max_le hsigma
      (max_le hP1 ((le_max_right _ _).trans hl)))))
  have hgap : max 0 caseIIGapC1 ≤ c1SingleBudget := max_le hP0 c1_gap_budget
  have hb' : max 0 caseBSourceC1 ≤ c1SingleBudget := max_le hP0 hb
  have hround : c1LogBudget sourceRoundedCutoff ≤ c1SingleBudget :=
    c1_log_budget (by unfold sourceRoundedCutoff; positivity) (tower_geometry.2.1.trans hu4)
  have herr : c1LogBudget (transportCaseIICutoff : ℝ) ≤ c1SingleBudget := c1_log_budget (Nat.cast_nonneg _) tower_transport.2
  have hrec : c1LogBudget (recursiveNatCutoff : ℝ) ≤ c1SingleBudget := c1_log_budget (Nat.cast_nonneg _) hr
  have hfull : c1LogBudget claim146FullCutoff ≤ c1SingleBudget :=
    c1_log_budget (zero_lt_one.trans claim146FullCutoff_gt_one).le (tower_claim146_cutoff.trans h14)
  have hexp : c1LogBudget (Real.exp 1) ≤ c1SingleBudget :=
    c1_log_budget (Real.exp_pos _).le ((tower_exp_small (by norm_num)).trans hu4)
  have hexp2 : c1LogBudget (Real.exp (max 1 (631360192512 : ℝ))) ≤ c1SingleBudget :=
    c1_log_budget (Real.exp_pos _).le ((tower_exp_small (by norm_num)).trans hu4)
  have hfour : c1LogBudget (4 : ℝ) ≤ c1SingleBudget := c1_log_budget (by norm_num) h4
  have hthree : (3 : ℝ) ≤ c1SingleBudget :=
    (by norm_num : (3 : ℝ) ≤ 10^100).trans (towerU_real_large.trans c1_U_budget)
  have hii : caseIIC1 ≤ 10*c1SingleBudget := by
    unfold caseIIC1
    norm_num only [Nat.reducePow,Nat.cast_ofNat]
    linarith only [hgap,hb',hround,herr,hrec,hfull,hexp,hexp2,hfour,hthree]
  have hp10 : c1SingleBudget ≤ 10*c1SingleBudget := by linarith only [hP0]
  have hall : numericalSuzukiC1 ≤ 10*c1SingleBudget := by
    unfold numericalSuzukiC1
    exact max_le (hP1.trans hp10) (max_le (hb.trans hp10) (max_le (hstrict.trans hp10) (max_le (heven.trans hp10) hii)))
  apply hall.trans
  unfold c1SingleBudget
  calc
    _ ≤ Real.exp 10*Real.exp (10^15 : ℝ) := mul_le_mul_of_nonneg_right
      (by linarith only [Real.add_one_le_exp (10 : ℝ)] : (10 : ℝ) ≤ Real.exp 10) (Real.exp_pos _).le
    _ = Real.exp (10+(10^15 : ℝ)) := by rw [Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by norm_num)

theorem numericalSuzukiC1_single_exp_cap : numericalSuzukiC1 ≤ Real.exp (10^40 : ℝ) :=
  numericalSuzukiC1_single_exp_sharp_cap.trans (Real.exp_le_exp.mpr (by norm_num))

#print axioms numericalSuzukiC1_single_exp_sharp_cap
end ChenEffective
