import NumericalSelbergDenominator

noncomputable section
namespace ChenEffective
open MathlibNt.SieveTheory
open LiuWeight SingularSeries
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option exponentiation.threshold 512
attribute [local irreducible] logPowerCutoff mertensProductThreshold

private opaque denominatorExponentCertificate : {k : ℕ // k=4000000000000} := ⟨4000000000000,rfl⟩
def numericalDenominatorExponent : ℕ := denominatorExponentCertificate.1
theorem numericalDenominatorExponent_eq : numericalDenominatorExponent=4000000000000 :=
  denominatorExponentCertificate.2
@[irreducible] def numericalDenominatorThreshold : ℕ := 3^(3^numericalDenominatorExponent)
theorem numericalDenominatorThreshold_eq : numericalDenominatorThreshold=3^(3^4000000000000) := by
  rw [numericalDenominatorThreshold,numericalDenominatorExponent_eq]

theorem selbergDenominatorThreshold_le_closed : selbergDenominatorThreshold ≤ numericalDenominatorThreshold := by
  have hM : mertensProductThreshold 2 ≤ 3^numericalDenominatorExponent := by
    unfold mertensProductThreshold
    apply max_le
    · unfold principalNumericalThreshold logPowerCutoff
      apply Nat.pow_le_pow_right (by norm_num : 1 ≤ (3 : ℕ))
      rw [numericalDenominatorExponent_eq]
      norm_num
    · apply Nat.pow_le_pow_right (by norm_num : 1 ≤ (3 : ℕ))
      rw [numericalDenominatorExponent_eq]
      norm_num
  have hE : selbergMertensEndpoint ≤ 3^numericalDenominatorExponent := by
    simpa only [selbergMertensEndpoint_eq] using hM
  have h6 : logPowerCutoff 6 ≤ 3^numericalDenominatorExponent := by
    unfold logPowerCutoff
    apply Nat.pow_le_pow_right (by norm_num : 1 ≤ (3 : ℕ))
    rw [numericalDenominatorExponent_eq]
    norm_num
  have h80 : 10^80 ≤ (3 : ℕ)^numericalDenominatorExponent := by
    calc
      _ ≤ ((3 : ℕ)^4)^80 := Nat.pow_le_pow_left (by norm_num : (10 : ℕ) ≤ 3^4) 80
      _ = 3^(4*80) := (pow_mul _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by rw [numericalDenominatorExponent_eq]; norm_num)
  unfold selbergDenominatorThreshold numericalDenominatorThreshold selbergDivisorThreshold
  exact max_le (Nat.pow_le_pow_right (by norm_num) (max_le hE h6))
    (Nat.pow_le_pow_right (by norm_num) h80)

/-- A literal integer cutoff for the Selberg denominator at epsilon=10^-10. -/
theorem numerical_selberg_denominator_closed {N : ℕ} (hN : numericalDenominatorThreshold ≤ N)
    (hEven : Even N) :
    Real.log N/((8+liuM1Delta)*liuSingularSeries N) ≤ liuSelbergDenominator N squareEpsilon :=
  numerical_selberg_denominator (selbergDenominatorThreshold_le_closed.trans hN) hEven

def squareThresholdFromPair (nPair : ℕ) : ℕ :=
  max squareAnalyticThreshold (max numericalDenominatorThreshold nPair)

/-- Only the finite genuine-li prime-pair premise remains. The denominator,
lambda admissibility, signed remainder and error coefficient are internal. -/
theorem numerical_square_from_prime_pair (nPair N : ℕ) (hN : squareThresholdFromPair nPair ≤ N)
    (hEven : Even N)
    (hpair : LiuGenuineLiWeightMainSumBound 2 (0.49254+liuM1Eta) N) :
    liuSelbergSquareCount N squareEpsilon (liuSelbergOptimalLambda N squareEpsilon) ≤
      (3.94033 : ℝ)*liuSingularSeries N*N/Real.log N^2+numericalSquareError*N/Real.log N^3 := by
  unfold squareThresholdFromPair at hN
  exact numerical_square_from_main_components N ((le_max_left _ _).trans hN) hEven
    (numerical_selberg_denominator_closed ((le_max_left _ _).trans ((le_max_right _ _).trans hN)) hEven) hpair

#print axioms numerical_selberg_denominator_closed
#print axioms numerical_square_from_prime_pair
end ChenEffective
