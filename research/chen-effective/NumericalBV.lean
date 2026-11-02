import NumericalLowConductor
import NumericalPrincipalPNT
import ExplicitBVAssembly

namespace ChenEffective
open AnalyticNumberTheory.LargeSieve
open MathlibNt.SieveTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def numericalBVThreshold (A : ℕ) : ℕ :=
  bvThreshold A
    (primitiveNumericalThreshold (A + highBVConductorExponent A + 5))
    (principalNumericalThreshold (A + 3))

def numericalBVConstant (A : ℕ) : ℝ :=
  bvConstant (primitiveNumericalConstant (highBVConductorExponent A)) principalNumericalConstant

theorem numerical_BV (A N : ℕ) (hN : numericalBVThreshold A ≤ N) :
    (∑ q ∈ Finset.Icc 1 (LiuWeight.panModulusCutoff N (highBVExponent A : ℝ)),
      BombieriVinogradov.standardPrimeAPPrefixMaxError N q) ≤
        numericalBVConstant A * (N : ℝ) / Real.log N ^ A := by
  apply explicit_BV_of_inputs A
    (primitiveNumericalThreshold (A + highBVConductorExponent A + 5))
    (principalNumericalThreshold (A + 3))
    (primitiveNumericalConstant (highBVConductorExponent A)) principalNumericalConstant
    (by unfold primitiveNumericalConstant; positivity)
    (by norm_num [principalNumericalConstant]) _ _ hN
  · intro M hM d hd ψ hψ
    have hd2 := (Finset.mem_Icc.mp hd).1
    let : NeZero d := ⟨by omega⟩
    exact numerical_primitive_low_conductor_cutoff hM (Finset.mem_Icc.mp hd).2 ψ hψ
  · intro M hM
    exact numerical_global_principal_source hM

theorem numerical_BV_constant_three : numericalBVConstant 3 = 1000344400000012180 := by
  norm_num [numericalBVConstant, bvConstant, primitiveNumericalConstant,
    principalNumericalConstant, highBVConductorExponent]

theorem numerical_BV_threshold_closed (A : ℕ) :
    numericalBVThreshold A = 3 ^ (16 * (384 * A + 13569) ^ 2) := by
  have hhigh : highBVThreshold A ≤
      primitiveNumericalThreshold (A + highBVConductorExponent A + 5) := by
    unfold highBVThreshold primitiveNumericalThreshold logPowerCutoff highBVConductorExponent
    apply Nat.pow_le_pow_right (by norm_num)
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    omega
  have hprincipal : principalNumericalThreshold (A + 3) ≤
      primitiveNumericalThreshold (A + highBVConductorExponent A + 5) := by
    unfold principalNumericalThreshold primitiveNumericalThreshold logPowerCutoff highBVConductorExponent
    apply Nat.pow_le_pow_right (by norm_num)
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    omega
  unfold numericalBVThreshold bvThreshold
  rw [max_eq_left hprincipal, max_eq_right hhigh]
  unfold primitiveNumericalThreshold logPowerCutoff highBVConductorExponent
  rw [show 128 * (A + 2 * (A + 50) + 5 + 1) + 1 = 384 * A + 13569 by omega]

#print axioms numerical_BV
end ChenEffective
