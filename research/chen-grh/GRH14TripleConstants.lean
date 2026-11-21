import GRH14SelbergRemainder

noncomputable section
namespace ChenEffective.GRH14
open Real
open MathlibNt.SieveTheory LiuWeight
open NumericalPanHigh
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem selberg_remainder_constant_cap : selbergRemainderConstant 5≤(1e12:ℝ) := by
  have hlog : 0<log (2:ℝ) := log_pos (by norm_num)
  have hq : (2:ℝ)/log 2≤4 := (div_le_iff₀ hlog).mpr (by linarith only [log_two_gt_d9])
  have hs : panSharpConstant≤32 := by unfold panSharpConstant; linarith only [pi_lt_four]
  have hshort : panShortConstant≤512 := by unfold panShortConstant; linarith only [hs]
  have hlong : panLongConstant≤2560 := by
    unfold panLongConstant
    calc
      _ ≤ (16:ℝ)*32*(1+4) := by gcongr
      _ = _ := by norm_num
  have he : exp (2:ℝ)≤9 := by
    rw [show (2:ℝ)=1+1 by norm_num,exp_add]
    nlinarith only [exp_one_lt_d9,exp_pos (1:ℝ)]
  have hlong0 : 0≤panLongConstant := by
    unfold panLongConstant
    have := panSharpConstant_pos
    positivity
  have hhigh : panHighConstant≤(1e9:ℝ) := by
    unfold panHighConstant panCellConstant
    calc
      _ ≤ (9:ℝ)*(36*512+36*9*2560) := by gcongr
      _ ≤ _ := by norm_num
  have hU : panUnweightedConstant 30≤(1e10:ℝ) := by
    unfold panUnweightedConstant panLedgerConstant panPrincipalConstant
    linarith only [hhigh]
  have hU0 := (panUnweightedConstant_pos 30).le
  have henv0 := (H30.panActualEnvelopeConstant_pos (2/log 2)).le
  have hLi : liuLogarithmicIntegralUpperConstant (2/log 2)≤10 := by
    unfold liuLogarithmicIntegralUpperConstant
    rw [abs_of_nonneg (by positivity : (0:ℝ)≤2/log 2)]
    linarith only [hq]
  have henv : H30.panActualEnvelopeConstant (2/log 2)≤26 := by
    unfold H30.panActualEnvelopeConstant liuPanLiEnvelopeConstant
    have hh : liuLogarithmicIntegralUpperConstant (2/log 2)/log 2≤20 :=
      (div_le_iff₀ hlog).mpr (by linarith only [hLi,log_two_gt_d9])
    linarith only [hh]
  have hD : panWeightedSquareConstant 5≤(1e10:ℝ)^2 := by
    unfold panWeightedSquareConstant
    norm_num only [panWeightedSaving,Nat.reduceMul,Nat.reduceAdd]
    calc
      _ ≤ (2:ℝ)^20*26*1e10 := by
        gcongr <;> norm_num
      _ ≤ _ := by norm_num
  have hW : panWeightedConstant 5≤(1e10:ℝ)+1 := by
    unfold panWeightedConstant
    have hh := Real.sqrt_le_iff.mpr ⟨(by norm_num : (0:ℝ)≤1e10),hD⟩
    linarith only [hh]
  have hgamma : exp eulerMascheroniConstant≤3 := by
    have hh : exp eulerMascheroniConstant≤exp 1 :=
      exp_le_exp.mpr (by linarith only [eulerMascheroniConstant_lt_two_thirds])
    exact hh.trans (by linarith only [exp_one_lt_d9])
  have hdiv : H30.panDivisorConstant≤216 := by
    unfold H30.panDivisorConstant
    calc
      _ ≤ ((2:ℝ)*3)^3 := by gcongr
      _ = _ := by norm_num
  have hdelta : |(2:ℝ)-2/log 2|≤2 := by
    rw [abs_le]
    constructor <;> linarith only [hq,div_nonneg (by norm_num : (0:ℝ)≤2) hlog.le]
  have hnorm : panNormalizationConstant≤1296 := by
    unfold panNormalizationConstant H30.panNormalizationConstant
    calc
      _ ≤ (3:ℝ)*216*2 := by gcongr
      _ = _ := by norm_num
  have hLi2 : liuLogarithmicIntegralUpperConstant 2≤8 := by
    norm_num only [liuLogarithmicIntegralUpperConstant,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith only [hq]
  unfold selbergRemainderConstant panCanonicalConstant
  linarith only [hW,hnorm,hLi2]

theorem selberg_remainder_paid {N : ℕ} (hN : targetCutoff≤N) :
    selbergRemainderConstant 5*N/log (N:ℝ)^5 ≤
      (1/500000:ℝ)*(SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2) := by
  have hL := target_log_lower hN
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hs := half_le_liuSingularSeries N
  have hc : selbergRemainderConstant 5/log (N:ℝ)^3 ≤
      (1/500000:ℝ)*SingularSeries.liuSingularSeries N := by
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1000000) hL 3
    apply (div_le_iff₀ (pow_pos hl 3)).mpr
    have hh := mul_le_mul hs hp (by norm_num : (0:ℝ)≤1000000^3)
      (SingularSeries.liuSingularSeries_pos N).le
    nlinarith only [hh,selberg_remainder_constant_cap]
  have hh := mul_le_mul_of_nonneg_right hc
    (show 0≤(N:ℝ)/log (N:ℝ)^2 by positivity)
  convert hh using 1 <;> field_simp [hl.ne']

#print axioms selberg_remainder_paid
end ChenEffective.GRH14

