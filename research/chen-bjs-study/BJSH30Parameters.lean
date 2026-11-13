import NumericalSquareAssembly

noncomputable section
namespace ChenEffective.H30
def squareEpsilonDenominator : ℕ := 100
def squareEpsilon : ℝ := 1/(squareEpsilonDenominator:ℝ)
private opaque analyticCertificate : {n : ℕ // n=5*10^12} := ⟨5*10^12,rfl⟩
def primePairPowerExponent : ℕ := analyticCertificate.1
theorem primePairPowerExponent_eq : primePairPowerExponent=5*10^12 := analyticCertificate.2
@[irreducible] def squareClosedThreshold : ℕ := 3^primePairPowerExponent
theorem squareClosedThreshold_eq : squareClosedThreshold=3^(5*10^12) := by
  unfold squareClosedThreshold
  rw [primePairPowerExponent_eq]
end ChenEffective.H30
