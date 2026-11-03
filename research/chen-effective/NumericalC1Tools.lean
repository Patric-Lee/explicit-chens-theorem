import NumericalC1Geometry
import NumericalC1Endpoint
import NumericalC1Scalar
import NumericalSigmaTwelveContraction
import NumericalSigmaZeroCutoff

open scoped Classical BigOperators Interval
open Set Filter Finset Topology MeasureTheory intervalIntegral
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LinearSieve MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem real_nat_three_pow_one (n : ℕ) : (1 : ℝ) ≤ ((3^n : ℕ) : ℝ) := by
  exact_mod_cast (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3) : 1 ≤ (3 : ℕ)^n)

theorem caseIEndpointC1_one : (1 : ℝ) ≤ caseIEndpointC1 := by
  unfold caseIEndpointC1 caseIOrderC1
  exact real_nat_three_pow_one _

theorem caseIScalarC1_one : (1 : ℝ) ≤ caseIScalarC1 := by
  unfold caseIScalarC1 logPowerCutoff
  exact real_nat_three_pow_one _

theorem numerical_endpoint_order_uniform (C1 K D A : ℝ)
    (hC1 : (caseIEndpointC1 : ℝ) ≤ C1) (hK : 2 ≤ K) (hD : 2 ≤ D)
    (_hA : 0 ≤ A) (hAcap : A ≤ 1 + 2*144*(reverseRatioCap : ℝ)+12*(reverseRatioCap : ℝ))
    (hlarge : C1*K^(7 : ℝ) < Real.log D) :
    ∃ q : Lemma144StrictFactor,
      q.ρ = (1+sigma12ContractionMultiplier (sourceSigma D 16) (1/2))/2 ∧
        caseISourceOrderCoefficient A D 16 ≤ 1-q.ρ := by
  have ha : A ≤ ((1+300*reverseRatioCap : ℕ) : ℝ) := by
    push_cast
    nlinarith only [hAcap]
  unfold caseIEndpointC1 at hC1
  exact numerical_caseI_order_gap (a := 1+300*reverseRatioCap) ha hC1 hK hD hlarge

theorem numerical_fixed_threshold {Θ D0 : ℝ} (hΘ : 0 < Θ) (hD0 : 0 < D0) :
    ∀ (C1 K D : ℝ), max 1 (Real.log D0) ≤ C1 → 2 ≤ K → 0 < D →
      C1*K^Θ < Real.log D → D0 < D := by
  intro C1 K D hC1 hK hD hlarge
  have hc1 : 1 ≤ C1 := (le_max_left _ _).trans hC1
  have hkpow : 1 ≤ K^Θ := Real.one_le_rpow (by linarith only [hK]) hΘ.le
  have hlog : Real.log D0 < Real.log D :=
    ((le_max_right _ _).trans hC1).trans_lt
      ((show C1 ≤ C1*K^Θ by nlinarith only [hc1, hkpow]).trans_lt hlarge)
  have hh := Real.exp_lt_exp.mpr hlog
  rwa [Real.exp_log hD0, Real.exp_log hD] at hh

noncomputable def caseIStrictDcut : ℝ := max 4
  (max claim146FullCutoff (max claim146FullCutoff (max preThresholdCutoff
    (max (recursiveNatCutoff : ℝ) (max ((transportQuotientCutoff^2 : ℕ) : ℝ) 4)))))
noncomputable def caseIEvenDcut : ℝ := max 4
  (max claim146FullCutoff (max claim146FullCutoff
    (max preThresholdCutoff (max (Real.exp (Real.exp 3))
      (max (recursiveNatCutoff : ℝ) ((transportQuotientCutoff^2 : ℕ) : ℝ))))))
noncomputable def caseIStrictC1 : ℝ := max 1 (max (caseIEndpointC1 : ℝ)
  (max (caseIScalarC1 : ℝ) (max sigmaZeroC1 (max 1 (Real.log caseIStrictDcut)))))
noncomputable def caseIEvenC1 : ℝ := max 1 (max (caseIEndpointC1 : ℝ)
  (max (caseIScalarC1 : ℝ) (max sigmaZeroC1 (max 1 (Real.log caseIEvenDcut)))))

#print axioms numerical_endpoint_order_uniform
end ChenEffective
