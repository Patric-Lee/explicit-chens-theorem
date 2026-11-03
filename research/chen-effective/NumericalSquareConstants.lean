import NumericalSelbergRemainder
import ExplicitChenTriple

noncomputable section
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiuWeight
open NumericalPanHigh
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def numericalSquareError : ℝ := selbergRemainderConstant 3
def numericalTripleErrorCap : ℕ := 10^40

theorem numerical_square_error_cap : numericalSquareError+19 ≤ numericalTripleErrorCap := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlong0 : 0 ≤ panLongConstant := by
    unfold panLongConstant
    have := panSharpConstant_pos
    positivity
  have hq : (2 : ℝ)/Real.log 2 ≤ 4 := (div_le_iff₀ hlog).mpr
    (by linarith only [Real.log_two_gt_d9])
  have hs : panSharpConstant ≤ 32 := by unfold panSharpConstant; linarith only [Real.pi_lt_four]
  have hshort : panShortConstant ≤ 512 := by unfold panShortConstant; linarith only [hs]
  have hlong : panLongConstant ≤ 2560 := by
    unfold panLongConstant
    calc
      _ ≤ (16 : ℝ)*32*(1+4) := by gcongr
      _ = _ := by norm_num
  have he : Real.exp (2 : ℝ) ≤ 9 := by
    rw [show (2 : ℝ) = 1+1 by norm_num, Real.exp_add]
    nlinarith only [Real.exp_one_lt_d9, Real.exp_pos (1 : ℝ)]
  have hhigh : panHighConstant ≤ 10^9 := by
    unfold panHighConstant panCellConstant
    calc
      _ ≤ (9 : ℝ)*(36*512+36*9*2560) := by
        gcongr
      _ ≤ _ := by norm_num
  have hlow : panLowConstant 28 34 ≤ 10^55 := by
    norm_num [panLowConstant, panMovingPrimeConstant, panPrimePrefixConstant, primitiveNumericalConstant]
  have hprincipal : panPrincipalConstant 28 ≤ 10^40 := by
    norm_num [panPrincipalConstant, panMovingPNTConstant, numericalBVConstant, bvConstant,
      primitiveNumericalConstant, principalNumericalConstant, highBVConductorExponent]
  have hU : panUnweightedConstant 26 ≤ 10^60 := by
    unfold panUnweightedConstant panLedgerConstant
    norm_num only [Nat.reduceAdd] at *
    linarith only [hlow, hprincipal, hhigh]
  have hU0 := (panUnweightedConstant_pos 26).le
  have henv0 := (panActualEnvelopeConstant_pos (2/Real.log 2)).le
  have henv : panActualEnvelopeConstant (2/Real.log 2) ≤ 26 := by
    have hLi : liuLogarithmicIntegralUpperConstant (2/Real.log 2) ≤ 10 := by
      unfold liuLogarithmicIntegralUpperConstant
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2/Real.log 2)]
      linarith only [hq]
    unfold panActualEnvelopeConstant liuPanLiEnvelopeConstant
    have hh : liuLogarithmicIntegralUpperConstant (2/Real.log 2)/Real.log 2 ≤ 20 :=
      (div_le_iff₀ hlog).mpr (by linarith only [hLi, Real.log_two_gt_d9])
    linarith only [hh]
  have hD : panWeightedSquareConstant 3 ≤ (10^35 : ℝ)^2 := by
    unfold panWeightedSquareConstant
    norm_num only [panWeightedSaving, Nat.reduceMul, Nat.reduceAdd]
    calc
      _ ≤ (2 : ℝ)^20*26*(10^60) := by
        gcongr
        norm_num
      _ ≤ _ := by norm_num
  have hW : panWeightedConstant 3 ≤ 10^35+1 := by
    unfold panWeightedConstant
    have hh := (Real.sqrt_le_iff).mpr ⟨(by norm_num : (0 : ℝ) ≤ 10^35), hD⟩
    linarith only [hh]
  have hgamma : Real.exp Real.eulerMascheroniConstant ≤ 3 := by
    have hh : Real.exp Real.eulerMascheroniConstant ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (by linarith only [Real.eulerMascheroniConstant_lt_two_thirds])
    exact hh.trans (by linarith only [Real.exp_one_lt_d9])
  have hdiv : panDivisorConstant ≤ 216 := by
    unfold panDivisorConstant
    calc
      _ ≤ ((2 : ℝ)*3)^3 := by gcongr
      _ = _ := by norm_num
  have hdelta : |(2 : ℝ)-2/Real.log 2| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith only [hq, div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlog.le]
  have hnorm : panNormalizationConstant ≤ 1296 := by
    unfold panNormalizationConstant
    calc
      _ ≤ (3 : ℝ)*216*2 := by gcongr
      _ = _ := by norm_num
  have hLi2 : liuLogarithmicIntegralUpperConstant 2 ≤ 8 := by
    norm_num only [liuLogarithmicIntegralUpperConstant, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith only [hq]
  unfold numericalSquareError selbergRemainderConstant panCanonicalConstant numericalTripleErrorCap
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  linarith only [hW, hnorm, hLi2]

#print axioms numerical_square_error_cap
end ChenEffective
