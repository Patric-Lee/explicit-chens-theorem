import NumericalRealLogBounds
import NumericalFiniteHat
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIAbsorption

namespace ChenEffective
open Real
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def caseIOrderC1 (a : ℕ) : ℕ := 3 ^ (4 * a + 1)

/-- The source-order absorption cutoff is numerical as soon as its amplitude is capped. -/
theorem numerical_caseI_order_gap {a : ℕ} {A C1 K D : ℝ}
    (hA : A ≤ a) (hC1 : (caseIOrderC1 a : ℝ) ≤ C1) (hK : 2 ≤ K) (hD : 2 ≤ D)
    (hlarge : C1 * K ^ (7 : ℝ) < Real.log D) :
    ∃ q : Lemma144StrictFactor,
      q.ρ = (1 + sigma12ContractionMultiplier (sourceSigma D 16) (1 / 2)) / 2 ∧
      caseISourceOrderCoefficient A D 16 ≤ 1 - q.ρ := by
  have hc0 : (0 : ℝ) < (caseIOrderC1 a : ℕ) := by
    exact_mod_cast (pow_pos (by norm_num : (0 : ℕ) < 3) (4 * a + 1))
  have hC10 : 0 ≤ C1 := hc0.le.trans hC1
  have hKpow : (1 : ℝ) ≤ K ^ (7 : ℝ) := Real.one_le_rpow (by linarith only [hK]) (by norm_num)
  have hx : (caseIOrderC1 a : ℝ) ≤ Real.log D := by
    apply hC1.trans
    have hh : C1 ≤ C1 * K ^ (7 : ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hKpow hC10
    exact hh.trans hlarge.le
  unfold caseIOrderC1 at hx
  have hll := real_log_ge_power_three (b := 4 * a + 1) (x := Real.log D) hx
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at hll
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hll1 : 1 ≤ Real.log (Real.log D) := by linarith only [hll, ha0]
  have hll0 : 0 < Real.log (Real.log D) := by linarith only [hll1]
  have hD0 : 0 < D := by linarith only [hD]
  have hlog0 : 0 < Real.log D := Real.log_pos (by linarith only [hD])
  have hlog1 : 1 ≤ Real.log D :=
    (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans
      ((Real.le_log_iff_exp_le hlog0).mp hll1)
  have hinner : Real.log D < Real.log (27 * D) :=
    Real.log_lt_log hD0 (by nlinarith only [hD0])
  have hll27 : 1 < Real.log (Real.log (27 * D)) :=
    hll1.trans_lt (Real.log_lt_log hlog0 hinner)
  have hp : (1 : ℝ) ≤ (Real.log D) ^ (1 / 16 : ℝ) :=
    Real.one_le_rpow hlog1 (by norm_num)
  have hsigma : 1 < sourceSigma D 16 := by
    unfold sourceSigma
    have hh := mul_le_mul_of_nonneg_right hp (show 0 ≤ Real.log (Real.log (27 * D)) by linarith only [hll27])
    linarith only [hh, hll27]
  have hsigma0 : 0 < sourceSigma D 16 := by linarith only [hsigma]
  obtain ⟨q, hq, hgap⟩ := caseI_midpoint_gap_lower
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hsigma
  refine ⟨q, hq, ?_⟩
  have hquarter : A / Real.log (Real.log D) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ hll0).mpr
    linarith only [hA, hll]
  unfold caseISourceOrderCoefficient
  calc
    _ = (A / Real.log (Real.log D)) / sourceSigma D 16 := by ring
    _ ≤ (1 / 4 : ℝ) / sourceSigma D 16 := div_le_div_of_nonneg_right hquarter hsigma0.le
    _ = (1 - (1 / 2 : ℝ)) / (2 * sourceSigma D 16) := by ring
    _ ≤ _ := hgap

theorem caseIOrderC1_finite_amplitude (r : ℕ) :
    caseIOrderC1 (1 + 300 * r) = 3 ^ (1200 * r + 5) := by
  unfold caseIOrderC1
  congr 1
  ring

/-- The actual endpoint coefficient with the proved finite-layer cap L=144. -/
theorem numerical_caseI_endpoint_gap {r : ℕ} {R C C1 K D : ℝ}
    (hR0 : 0 ≤ R) (hR : R ≤ r) (hC : 3 ≤ C)
    (hC1 : (caseIOrderC1 (1 + 300 * r) : ℝ) ≤ C1) (hK : 2 ≤ K) (hD : 2 ≤ D)
    (hlarge : C1 * K ^ (7 : ℝ) < Real.log D) :
    ∃ q : Lemma144StrictFactor,
      q.ρ = (1 + sigma12ContractionMultiplier (sourceSigma D 16) (1 / 2)) / 2 ∧
      caseISourceOrderCoefficient (1 / C + 864 * R / (C * Real.exp (Real.sqrt K)) + 12 * R) D 16 ≤
        1 - q.ρ := by
  apply numerical_caseI_order_gap (a := 1 + 300 * r) _ hC1 hK hD hlarge
  have hcoeff := caseI_endpointCoefficient_le_commonScale
    (A := (1 : ℝ)) (C := C) (C145 := 1) (K := K) (L := 144) (R := R)
    (by norm_num) hC (by linarith only [hC]) (by norm_num) hR0
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
  nlinarith only [hcoeff, hR]

#print axioms numerical_caseI_order_gap
#print axioms numerical_caseI_endpoint_gap
end ChenEffective
