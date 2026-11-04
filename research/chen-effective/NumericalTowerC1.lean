import NumericalTowerHeads

noncomputable section
namespace ChenEffective
open Real Set Finset
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
attribute [local irreducible] logPowerCutoff

theorem tower_exp_small {x : ℝ} (hx : x ≤ 10^12) : Real.exp x ≤ towerU :=
  (Real.exp_le_exp.mpr hx).trans exp_seed_le_towerU

theorem tower_exp_three : Real.exp (3 : ℝ) ≤ 27 := by
  have hh := exp_le_three_pow (n := 3) (x := 3) (by norm_num)
  norm_num at hh ⊢
  exact hh

theorem tower_log27 : Real.log (27 : ℝ) ≤ towerU :=
  (tower_log_le_self (by norm_num)).trans ((by norm_num : (27 : ℝ) ≤ 10^100).trans towerU_real_large)

theorem tower_geometry : sourceGeometryCutoff ≤ towerU ∧ sourceRoundedCutoff ≤ towerU ∧ recursiveNatCutoff ≤ towerU := by
  have hee : Real.exp (Real.exp 3) ≤ towerU := tower_exp_small (tower_exp_three.trans (by norm_num))
  let C : ℝ := max 1 (2*Real.log 2/((1-1/16)/2))
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC5 : C ≤ 5 := by
    dsimp [C]
    apply max_le (by norm_num)
    norm_num
    linarith only [Real.log_two_lt_d9]
  have hpow : C^(32/15 : ℝ) ≤ 125 := by
    have hh := (Real.rpow_le_rpow (zero_le_one.trans hC1) hC5 (by norm_num : (0 : ℝ) ≤ 32/15)).trans
      (tower_rpow_le_nat (u := 5) (n := 3) (by norm_num) (by norm_num : (32/15 : ℝ) ≤ 3))
    norm_num at hh ⊢
    exact hh
  have hSigma : sourceSigmaTwoCutoff 16 ≤ towerU := by
    have hh : Real.exp (max 2 (max (Real.log 27) (C^(32/15 : ℝ)))) ≤ towerU := by
      apply tower_exp_small
      apply max_le (by norm_num)
      exact max_le ((tower_log_le_self (by norm_num)).trans (by norm_num)) (hpow.trans (by norm_num))
    norm_num [sourceSigmaTwoCutoff,C] at hh ⊢
    exact hh
  have hgeo : sourceGeometryCutoff ≤ towerU := max_le hee hSigma
  have hrounded : sourceRoundedCutoff ≤ towerU := by
    unfold sourceRoundedCutoff
    exact max_le hgeo (max_le ((by norm_num : (8 : ℝ) ≤ 10^100).trans towerU_real_large)
      (max_le (tower_exp_small (by norm_num)) (max_le
        (tower_exp_small (by have h := Real.log_two_lt_d9; linarith only [h]))
        (tower_exp_small (by norm_num)))))
  have hrec : recursiveCoordinateCutoff ≤ towerU := by
    unfold recursiveCoordinateCutoff
    rw [← Real.exp_nat_mul]
    have hi : Real.exp (2/(1-1/(16 : ℝ))) ≤ 27 :=
      (Real.exp_le_exp.mpr (by norm_num)).trans tower_exp_three
    apply tower_exp_small
    norm_num only [Nat.cast_ofNat]
    linarith only [hi]
  exact ⟨hgeo,hrounded,Nat.ceil_le.mpr hrec⟩

theorem tower_caseB : caseBSourceC1 ≤ towerH := by
  have hl2 : (1/2 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hl20 : 0 < Real.log (2 : ℝ) := by linarith only [hl2]
  have hl21 : Real.log (2 : ℝ) ≤ 1 := by linarith only [Real.log_two_lt_d9]
  have hi : 1/Real.log (2 : ℝ) ≤ 2 := (div_le_iff₀ hl20).mpr (by linarith only [hl2])
  have hll : |Real.log (Real.log 2)| ≤ 1 := by
    have h1 := Real.log_le_log (by norm_num : (0 : ℝ) < 1/2) hl2
    have h2 := Real.log_nonpos hl20.le hl21
    rw [Real.log_div (by norm_num) (by norm_num),Real.log_one] at h1
    rw [abs_le]
    constructor <;> linarith only [h1,h2,hl21]
  have hlg : |Real.log (1+1/Real.log 2)| ≤ 2 := by
    have h0 : 0 ≤ Real.log (1+1/Real.log 2) := Real.log_nonneg (le_add_of_nonneg_right (by positivity))
    have hh := Real.log_le_sub_one_of_pos (show 0 < 1+1/Real.log 2 by positivity)
    rw [abs_of_nonneg h0]
    linarith only [hh,hi]
  let B := |Real.log (1+1/Real.log 2)|+2*|Real.log (Real.log 2)|
  let Q := max 6 (max (B+2) (max (B+9) (Real.exp 1+2)))
  have hB : B ≤ 4 := by dsimp [B]; linarith only [hll,hlg]
  have hQ : Q ≤ 20 := by
    dsimp [Q]
    have he := Real.exp_one_lt_d9
    exact max_le (by norm_num) (max_le (by linarith only [hB]) (max_le (by linarith only [hB]) (by linarith only [he])))
  have hinner : Real.exp ((100+2+Real.log 2)/(16-4)) ≤ towerU := by
    apply tower_exp_small
    norm_num
    linarith only [hl21]
  change max (Real.exp (max 20000 (max (Real.exp ((100+2+Real.log 2)/(16-4))) Q)))
    (max (Real.exp 100000) (max 2 (Real.log 27))) ≤ towerH
  apply max_le
  · apply exp_U_pow_le_H (n := 1) (by norm_num)
    simpa only [pow_one] using max_le ((by norm_num : (20000 : ℝ) ≤ 10^100).trans towerU_real_large)
      (max_le hinner (hQ.trans ((by norm_num : (20 : ℝ) ≤ 10^100).trans towerU_real_large)))
  · exact max_le ((tower_exp_small (by norm_num)).trans towerU_le_H)
      (max_le ((by norm_num : (2 : ℝ) ≤ 10^100).trans towerH_large) (tower_log27.trans towerU_le_H))

theorem tower_caseII_gap : caseIIGapC1 ≤ towerH := by
  have hsqrt : ((3 : ℝ)/2)^(1/2 : ℝ) ≤ 2 := by
    have hh := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 3/2) (by norm_num : (3/2 : ℝ) ≤ 4) (by norm_num : (0 : ℝ) ≤ 1/2)
    norm_num at hh ⊢
    exact hh
  have hM : caseIIGapAmplitude ≤ 10^12 := by
    unfold caseIIGapAmplitude
    norm_num only [Real.rpow_ofNat,Nat.reducePow]
    linarith only [hsqrt]
  have hcore : coreDecayCutoff caseIIGapAmplitude ≤ towerH := by
    have hbase : max 1 (128*caseIIGapAmplitude/(5*(1-(1/2 : ℝ)))) ≤ towerU := by
      apply max_le towerU_one
      have hu := towerU_real_large
      norm_num
      linarith only [hM,hu]
    have hpow : (max 1 (128*caseIIGapAmplitude/(5*(1-(1/2 : ℝ)))))^
        (1/((1-(1/2 : ℝ))-(2/7+3/16))) ≤ towerH := by
      apply le_trans _ (towerU_pow_le_H (n := 40) (by norm_num))
      apply (Real.rpow_le_rpow (zero_le_one.trans (le_max_left _ _)) hbase (by norm_num)).trans
      exact tower_rpow_le_nat towerU_one (by norm_num : (1/((1-(1/2 : ℝ))-(2/7+3/16))) ≤ (40 : ℕ))
    have hlog : (coreDecayLogCutoff : ℝ) ≤ towerU := by
      have hh : coreDecayLogCutoff ≤ towerU := by
        unfold coreDecayLogCutoff logPowerCutoff towerU
        apply Nat.pow_le_pow_right (by norm_num)
        rw [towerSeed_eq]
        norm_num
      exact_mod_cast hh
    unfold coreDecayCutoff
    exact max_le (max_le ((by norm_num : (2 : ℝ) ≤ 10^100).trans towerH_large) (tower_log27.trans towerU_le_H))
      (max_le (hlog.trans towerU_le_H) hpow)
  unfold caseIIGapC1
  exact max_le hcore (max_le ((tower_exp_small (by norm_num)).trans towerU_le_H)
    ((by norm_num : (3 : ℝ)^(16 : ℝ) ≤ 10^100).trans towerH_large))

theorem tower_transport : (transportQuotientCutoff : ℝ) ≤ (towerH : ℝ)^2 ∧
    (transportCaseIICutoff : ℝ) ≤ (towerH : ℝ)^4 := by
  have hu := towerH_large
  have hh : Real.exp (3*((1+3*(16 : ℝ))*4^(16 : ℝ))) ≤ towerH :=
    (tower_exp_small (by norm_num)).trans towerU_le_H
  have hceil : ⌈max claim146FullCutoff (Real.exp (3*((1+3*(16 : ℝ))*4^(16 : ℝ))))⌉₊ ≤ towerH :=
    Nat.ceil_le.mpr (max_le tower_claim146_cutoff hh)
  have hceilR : (transportQuotientCutoff : ℝ) ≤ (towerH : ℝ)+1 := by
    unfold transportQuotientCutoff
    exact_mod_cast Nat.add_le_add_right hceil 1
  have h1 : (transportQuotientCutoff : ℝ) ≤ (towerH : ℝ)^2 := by
    have hp := sq_nonneg ((towerH : ℝ)-1)
    nlinarith only [hceilR,hu,hp]
  refine ⟨h1,?_⟩
  unfold transportCaseIICutoff
  rw [Nat.cast_max,Nat.cast_pow]
  have hrec : (recursiveNatCutoff : ℝ) ≤ towerU := by exact_mod_cast tower_geometry.2.2
  have hH14 : (towerH : ℝ) ≤ (towerH : ℝ)^4 := by simpa only [pow_one] using pow_le_pow_right₀ towerH_one (show 1 ≤ 4 by norm_num)
  exact max_le (by simpa only [← pow_mul] using pow_le_pow_left₀ (Nat.cast_nonneg transportQuotientCutoff) h1 2)
    (hrec.trans (towerU_le_H.trans hH14))

theorem tower_endpoint_caps : (caseIEndpointC1 : ℝ) ≤ towerH ∧ (caseIScalarC1 : ℝ) ≤ towerU := by
  constructor
  · rw [caseIEndpointC1_eq]
    have hn : 1200*reverseRatioCap+5 ≤ towerU := by
      have hh : 1200*reverseRatioCap+5 ≤ 10^100 := by norm_num [reverseRatioCap]
      exact hh.trans towerU_large
    have hp := Nat.pow_le_pow_right (show 1 ≤ (3 : ℕ) by norm_num)
      (hn.trans (by exact_mod_cast (show (towerU : ℝ) ≤ (towerU : ℝ)^100 by simpa only [pow_one] using pow_le_pow_right₀ towerU_one (show 1 ≤ 100 by norm_num))))
    unfold towerH
    exact_mod_cast hp
  · rw [caseIScalarC1_eq]
    have hp : 3^9461776 ≤ towerU := by unfold towerU; apply Nat.pow_le_pow_right (by norm_num); rw [towerSeed_eq]; norm_num
    exact_mod_cast hp

theorem tower_numerical_C1 : numericalSuzukiC1 ≤ (towerH : ℝ)^6 := by
  have hH1 := towerH_one
  have hH := towerH_large
  have h14 : (towerH : ℝ) ≤ (towerH : ℝ)^4 := by simpa only [pow_one] using pow_le_pow_right₀ hH1 (show 1 ≤ 4 by norm_num)
  have h46 : (towerH : ℝ)^4 ≤ (towerH : ℝ)^6 := pow_le_pow_right₀ hH1 (by norm_num)
  have hU4 : (towerU : ℝ) ≤ (towerH : ℝ)^4 := towerU_le_H.trans h14
  have h4 : (4 : ℝ) ≤ (towerH : ℝ)^4 := (by norm_num : (4 : ℝ) ≤ 10^100).trans (hH.trans h14)
  have hRec : (recursiveNatCutoff : ℝ) ≤ (towerH : ℝ)^4 := by
    have hh : (recursiveNatCutoff : ℝ) ≤ towerU := by exact_mod_cast tower_geometry.2.2
    exact hh.trans hU4
  have hQ : ((transportQuotientCutoff^2 : ℕ) : ℝ) ≤ (towerH : ℝ)^4 := by
    rw [Nat.cast_pow]
    simpa only [← pow_mul] using pow_le_pow_left₀ (Nat.cast_nonneg _) tower_transport.1 2
  have hFull := tower_claim146_cutoff.trans h14
  have hPre : preThresholdCutoff ≤ (towerH : ℝ)^4 := max_le (tower_geometry.1.trans hU4) h4
  have hEE : Real.exp (Real.exp 3) ≤ (towerH : ℝ)^4 :=
    (tower_exp_small (tower_exp_three.trans (by norm_num))).trans hU4
  have hStrictD : caseIStrictDcut ≤ (towerH : ℝ)^4 :=
    max_le h4 (max_le hFull (max_le hFull (max_le hPre (max_le hRec (max_le hQ h4)))))
  have hEvenD : caseIEvenDcut ≤ (towerH : ℝ)^4 :=
    max_le h4 (max_le hFull (max_le hFull (max_le hPre (max_le hEE (max_le hRec hQ)))))
  have hSigma : sigmaZeroC1 ≤ (towerH : ℝ)^4 := by
    unfold sigmaZeroC1
    rw [Real.log_exp]
    exact max_le (tower_caseB.trans h14) ((tower_exp_small (by norm_num)).trans hU4)
  have hStrict : caseIStrictC1 ≤ (towerH : ℝ)^4 := by
    have hl := (tower_log_le_self (show 0 < caseIStrictDcut from lt_of_lt_of_le (by norm_num) (le_max_left _ _))).trans hStrictD
    unfold caseIStrictC1
    exact max_le (one_le_pow₀ hH1) (max_le (tower_endpoint_caps.1.trans h14)
      (max_le (tower_endpoint_caps.2.trans hU4) (max_le hSigma (max_le (one_le_pow₀ hH1) hl))))
  have hEven : caseIEvenC1 ≤ (towerH : ℝ)^4 := by
    have hl := (tower_log_le_self (show 0 < caseIEvenDcut from lt_of_lt_of_le (by norm_num) (le_max_left _ _))).trans hEvenD
    unfold caseIEvenC1
    exact max_le (one_le_pow₀ hH1) (max_le (tower_endpoint_caps.1.trans h14)
      (max_le (tower_endpoint_caps.2.trans hU4) (max_le hSigma (max_le (one_le_pow₀ hH1) hl))))
  have hGap : max 0 caseIIGapC1 ≤ (towerH : ℝ)^4 := max_le (by positivity) (tower_caseII_gap.trans h14)
  have hB : max 0 caseBSourceC1 ≤ (towerH : ℝ)^4 := max_le (by positivity) (tower_caseB.trans h14)
  have hRound : c1LogBudget sourceRoundedCutoff ≤ (towerH : ℝ)^4 :=
    c1LogBudget_le (by unfold sourceRoundedCutoff; positivity) (one_le_pow₀ hH1) (tower_geometry.2.1.trans hU4)
  have hFull' : c1LogBudget claim146FullCutoff ≤ (towerH : ℝ)^4 :=
    c1LogBudget_le (zero_lt_one.trans claim146FullCutoff_gt_one).le (one_le_pow₀ hH1) hFull
  have hExp : c1LogBudget (Real.exp 1) ≤ (towerH : ℝ)^4 :=
    c1LogBudget_le (Real.exp_pos _).le (one_le_pow₀ hH1) ((tower_exp_small (by norm_num)).trans hU4)
  have hExp2 : c1LogBudget (Real.exp (max 1 (631360192512 : ℝ))) ≤ (towerH : ℝ)^4 :=
    c1LogBudget_le (Real.exp_pos _).le (one_le_pow₀ hH1) ((tower_exp_small (by norm_num)).trans hU4)
  have hErrLog : c1LogBudget (transportCaseIICutoff : ℝ) ≤ (towerH : ℝ)^4 :=
    c1LogBudget_le (Nat.cast_nonneg _) (one_le_pow₀ hH1) tower_transport.2
  have hRecLog : c1LogBudget (recursiveNatCutoff : ℝ) ≤ (towerH : ℝ)^4 :=
    c1LogBudget_le (Nat.cast_nonneg _) (one_le_pow₀ hH1) hRec
  have hFourLog : c1LogBudget (4 : ℝ) ≤ (towerH : ℝ)^4 :=
    c1LogBudget_le (by norm_num) (one_le_pow₀ hH1) h4
  have hII10 : caseIIC1 ≤ 10*(towerH : ℝ)^4 := by
    unfold caseIIC1
    norm_num only [Nat.reducePow,Nat.cast_ofNat]
    nlinarith only [hGap,hB,hRound,hErrLog,hRecLog,hFull',hExp,hExp2,hFourLog,h4]
  have hII : caseIIC1 ≤ (towerH : ℝ)^6 := by
    apply hII10.trans
    calc
      _ ≤ (towerH : ℝ)^2*(towerH : ℝ)^4 := mul_le_mul_of_nonneg_right
        (by nlinarith only [hH,sq_nonneg ((towerH : ℝ)-1)] : (10 : ℝ) ≤ (towerH : ℝ)^2) (by positivity)
      _ = _ := by ring
  unfold numericalSuzukiC1
  exact max_le (one_le_pow₀ hH1) (max_le (tower_caseB.trans (h14.trans h46))
    (max_le (hStrict.trans h46) (max_le (hEven.trans h46) hII)))

#print axioms tower_transport
/-- A logarithmic cap for the common threshold envelope. -/
theorem towerH_log_six_cap : Real.log ((towerH : ℝ)^6) ≤ Real.exp (10^15 : ℝ) := by
  have h3 : Real.log (3 : ℝ) ≤ 2 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<3)]
  have hlogU : Real.log (towerU : ℝ) ≤ 2*(10^12 : ℝ) := by
    rw [towerU,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,towerSeed_eq]
    norm_num only [Nat.cast_pow,Nat.cast_ofNat]
    nlinarith only [h3]
  have hU100 : (towerU : ℝ)^100 ≤ Real.exp (2*(10^14 : ℝ)) := by
    apply (Real.log_le_iff_le_exp (pow_pos towerU_pos 100)).mp
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hlogU]
  have hlogH : Real.log ((towerH : ℝ)^6) = 6*(towerU : ℝ)^100*Real.log 3 := by
    rw [Real.log_pow,towerH,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
    push_cast
    ring
  have hmain : Real.log ((towerH : ℝ)^6) ≤ Real.exp (10^15 : ℝ) := by
    calc
      _ = 6*(towerU : ℝ)^100*Real.log 3 := hlogH
      _ ≤ 12*(towerU : ℝ)^100 := by
        have h := mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ 6*(towerU : ℝ)^100 by positivity)
        nlinarith only [h]
      _ ≤ 12*Real.exp (2*(10^14 : ℝ)) := mul_le_mul_of_nonneg_left hU100 (by norm_num)
      _ ≤ Real.exp 12*Real.exp (2*(10^14 : ℝ)) := mul_le_mul_of_nonneg_right
        (by linarith only [Real.add_one_le_exp (12 : ℝ)] : (12 : ℝ) ≤ Real.exp 12) (Real.exp_pos _).le
      _ = Real.exp (12+2*(10^14 : ℝ)) := by rw [Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by norm_num)
  exact hmain
#print axioms tower_numerical_C1
#print axioms towerH_log_six_cap
end ChenEffective
