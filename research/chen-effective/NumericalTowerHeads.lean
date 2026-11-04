import NumericalTowerSource

noncomputable section
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open BridgeAssembly CutoffCorrectedRatio SourceClaim146AssemblyNext
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem tower_perturbation {p q : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ (towerU : ℝ)^2)
    (hl0 : 0 < Real.log q) (hl : 1/Real.log q ≤ (towerU : ℝ)^2) : perturbationCutoff 16 p q ≤ towerH := by
  have hu1 := towerU_one
  have hu2 : (2 : ℝ) ≤ towerU := (by norm_num : (2 : ℝ) ≤ 10^100).trans towerU_real_large
  have hpow : p^(17 : ℝ) ≤ (towerU : ℝ)^34 := by
    have hh := pow_le_pow_left₀ hp0 hp 17
    simpa only [Real.rpow_ofNat,← pow_mul] using hh
  have hprod : 2*p^(17 : ℝ)/Real.log q ≤ (towerU : ℝ)^37 := by
    calc
      _ = 2*(p^(17 : ℝ))*(1/Real.log q) := by ring
      _ ≤ 2*(towerU : ℝ)^34*(towerU : ℝ)^2 := by gcongr
      _ = 2*(towerU : ℝ)^36 := by ring
      _ ≤ _ := tower_poly_absorb hu1 hu2 (by norm_num)
  unfold perturbationCutoff
  norm_num only [show (16 : ℝ)+1=17 by norm_num]
  exact exp_U_pow_le_H (n := 37) (by norm_num) (max_le (one_le_pow₀ hu1) hprod)

theorem tower_head_add_two {M : ℝ} (hM : M ≤ towerU) : M+2 ≤ (towerU : ℝ)^2 := by
  have hu := towerU_real_large
  have hp := mul_nonneg (show 0 ≤ (towerU : ℝ)-2 by linarith only [hu]) (show 0 ≤ (towerU : ℝ)-2 by linarith only [hu])
  nlinarith only [hM,hu,hp]

theorem tower_weighted_head {M : ℝ} (hM4 : 4 ≤ M) (hM : M ≤ towerU) : weightedHeadCutoff M ≤ towerH := by
  let a := (1-1/(M+2))^(1/4 : ℝ)
  let R := 1-1/(8*M)
  let q := (R+a)/(2*a)
  let k := (R+a)/(2*R)
  obtain ⟨hl0,hl,hk⟩ := tower_weighted_head_gaps hM4
  have hsmall : 96*M ≤ (towerU : ℝ)^2 := by
    have hu := towerU_real_large
    have hh := mul_le_mul_of_nonneg_left hM (by norm_num : (0 : ℝ) ≤ 96)
    have hp := mul_nonneg (show 0 ≤ (towerU : ℝ)-96 by linarith only [hu]) towerU_pos.le
    nlinarith only [hh,hp]
  have hform : weightedHeadCutoff M = max (max 2 (perturbationCutoff 16 (M+2) q)) (sourceLowerCutoff (2/(1-k))) := by
    dsimp only [weightedHeadCutoff,q,k,R,a]
    norm_num only [show (1-(1/2 : ℝ))=1/2 by norm_num,show (1/2 : ℝ)/2=1/4 by norm_num]
    rw [show (1/2 : ℝ)/(4*M)=1/(8*M) by field_simp; norm_num]
  rw [hform]
  exact max_le (max_le ((by norm_num : (2 : ℝ) ≤ 10^100).trans towerH_large)
    (tower_perturbation (by linarith only [hM4]) (tower_head_add_two hM) hl0 (hl.trans hsmall)))
    (tower_source_lower (hk.trans hsmall))

theorem tower_tail_head : claim146TailHead ≤ towerU := by
  unfold claim146TailHead
  apply max_le
  · have hh : claim146iiiFixedM hatTailCoefficient (1/2) ≤ (10^100 : ℝ) := by
      norm_num [claim146iiiFixedM,hatTailCoefficient,hatShiftCoefficient]
    exact hh.trans towerU_real_large
  · exact max_le tower_source_head ((Real.exp_le_exp.mpr (by norm_num : (2309 : ℝ) ≤ 10^18)).trans exp_seed_le_towerU)

theorem tower_tail_head_four : 4 ≤ claim146TailHead := by
  have hh : Real.exp 2309 ≤ claim146TailHead := (le_max_right _ _).trans (le_max_right _ _)
  have he := Real.add_one_le_exp (2309 : ℝ)
  linarith only [hh,he]

theorem tower_perturbation_two {M : ℝ} (hM4 : 4 ≤ M) (hM : M ≤ towerU) : perturbationCutoff 16 (M+2) 2 ≤ towerH := by
  have hl0 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hi : 1/Real.log (2 : ℝ) ≤ 2 := (div_le_iff₀ hl0).mpr (by linarith only [Real.log_two_gt_d9])
  exact tower_perturbation (by linarith only [hM4]) (tower_head_add_two hM) hl0
    (hi.trans (by have hu := towerU_real_large; nlinarith only [hu,sq_nonneg ((towerU : ℝ)-1)]))

theorem tower_derivative_cutoff : derivativeCutoff ≤ towerH := by
  have hm : derivativeHead ≤ towerU := by
    apply Nat.ceil_le.mpr
    exact max_le ((by norm_num : (16 : ℝ) ≤ 10^100).trans towerU_real_large) tower_source_head
  have hmR : (derivativeHead : ℝ) ≤ towerU := by exact_mod_cast hm
  have hm0 : 0 ≤ (derivativeHead : ℝ) := Nat.cast_nonneg _
  have hu := towerU_real_large
  have h1 : 1+16*(derivativeHead : ℝ) ≤ (towerU : ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_left hmR (by norm_num : (0 : ℝ) ≤ 16)
    have hp := mul_nonneg (show 0 ≤ (towerU : ℝ)-17 by linarith only [hu]) towerU_pos.le
    nlinarith only [hh,hp,hu]
  have h2 : (derivativeHead : ℝ)+1 ≤ (towerU : ℝ)^2 := by
    have hh := tower_head_add_two hmR
    linarith only [hh]
  have h3 : 51200000000*(derivativeHead : ℝ) ≤ (towerU : ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_left hmR (by norm_num : (0 : ℝ) ≤ 51200000000)
    have hp := mul_nonneg (show 0 ≤ (towerU : ℝ)-51200000000 by linarith only [hu]) towerU_pos.le
    nlinarith only [hh,hp]
  have hp : ((1+(derivativeHead : ℝ)*16)*((derivativeHead : ℝ)+1)^(16 : ℝ))/compactDerivativeFloor derivativeHead ≤ (towerU : ℝ)^36 := by
    unfold compactDerivativeFloor
    simp only [div_eq_mul_inv,one_mul,inv_inv]
    have hpow : ((derivativeHead : ℝ)+1)^(16 : ℝ) ≤ (towerU : ℝ)^32 := by
      have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (derivativeHead : ℝ)+1) h2 16
      simpa only [Real.rpow_ofNat,← pow_mul] using hh
    have h1' : 1+(derivativeHead : ℝ)*16 ≤ (towerU : ℝ)^2 := by nlinarith only [h1]
    calc
      _ ≤ (towerU : ℝ)^2*(towerU : ℝ)^32*(towerU : ℝ)^2 := by gcongr
      _ = _ := by ring
  unfold derivativeCutoff compactDerivativeCutoff
  exact max_le tower_source_ratio_cutoff (exp_U_pow_le_H (n := 36) (by norm_num) (max_le (one_le_pow₀ towerU_one) hp))

theorem tower_claim146_cutoff : claim146FullCutoff ≤ towerH := by
  have hmon : claim146MonotoneCutoff ≤ towerH := by
    unfold claim146MonotoneCutoff
    apply max_le tower_derivative_cutoff
    apply exp_U_pow_le_H (n := 1) (by norm_num)
    have hh := towerU_real_large
    norm_num at hh ⊢
    linarith only [hh]
  have htail : claim146TailCutoff ≤ towerH := by
    have hM := tower_tail_head
    have hM4 := tower_tail_head_four
    have hM2 : claim146TailHead ≤ (towerU : ℝ)^2 := hM.trans (by nlinarith only [towerU_one])
    have hlower := tower_source_lower hM2
    have hlower2 := tower_source_lower (tower_head_add_two hM)
    have hmove : movingTailCutoff claim146TailHead ≤ towerH := by
      unfold movingTailCutoff
      apply max_le (max_le tower_source_ratio_cutoff hlower)
      apply exp_U_pow_le_H (n := 16) (by norm_num)
      have hh := pow_le_pow_left₀ (by linarith only [hM4] : 0 ≤ claim146TailHead) hM 16
      simpa only [Real.rpow_ofNat] using hh
    unfold claim146TailCutoff
    exact max_le (tower_perturbation_two hM4 hM) (max_le (tower_weighted_head hM4 hM)
      (max_le hmove (max_le hmove hlower2)))
  exact max_le hmon htail

#print axioms tower_claim146_cutoff
end ChenEffective
