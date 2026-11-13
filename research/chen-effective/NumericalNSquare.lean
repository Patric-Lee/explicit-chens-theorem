import NumericalSquareThresholdCap

noncomputable section
namespace ChenEffective
open MathlibNt.SieveTheory
open LiuWeight SingularSeries SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
set_option exponentiation.threshold 512
attribute [local irreducible] logPowerCutoff mertensProductThreshold

theorem numerical_pair_power_le_denominator : 3^primePairPowerExponent ≤ numericalDenominatorThreshold := by
  have hE : primePairPowerExponent ≤ 3^numericalDenominatorExponent := by
    rw [primePairPowerExponent_eq]
    calc
      _ ≤ ((3 : ℕ)^4)^80 := Nat.pow_le_pow_left (by norm_num : (10 : ℕ) ≤ 3^4) 80
      _ = 3^(4*80) := (pow_mul _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by rw [numericalDenominatorExponent_eq]; norm_num)
  unfold numericalDenominatorThreshold
  exact Nat.pow_le_pow_right (by norm_num) hE

private theorem mertens_threshold_cap_for_pair {r k : ℕ}
    (hlog : 16*(128*(1+1)+1)^2 ≤ k) (hpow : 1800000000004*r ≤ k) :
    mertensProductThreshold r ≤ 3^k := by
  unfold mertensProductThreshold principalNumericalThreshold
  exact max_le (numerical_log_cutoff_cap _ _ hlog)
    (Nat.pow_le_pow_right (by norm_num) hpow)

theorem numerical_prime_pair_threshold_le_denominator : primePairThreshold ≤ numericalDenominatorThreshold := by
  have hM : selbergMertensEndpoint ≤ 3^numericalDenominatorExponent := by
    rw [selbergMertensEndpoint_eq]
    exact mertens_threshold_cap_for_pair
      (by rw [numericalDenominatorExponent_eq]; norm_num)
      (by rw [numericalDenominatorExponent_eq]; norm_num)
  have hK : numericalDenominatorExponent*10 ≤ 3^numericalDenominatorExponent := by
    calc
      _ ≤ (3 : ℕ)^100 := by rw [numericalDenominatorExponent_eq]; norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by rw [numericalDenominatorExponent_eq]; norm_num)
  unfold primePairThreshold
  apply max_le _ numerical_pair_power_le_denominator
  unfold numericalDenominatorThreshold
  calc
    _ ≤ (3^numericalDenominatorExponent)^10 := Nat.pow_le_pow_left hM 10
    _ = 3^(numericalDenominatorExponent*10) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hK

/-- A fully numerical square threshold, with no analytic premises remaining. -/
def nSquare : ℕ := numericalDenominatorThreshold
theorem nSquare_eq : nSquare=3^(3^4000000000000) := numericalDenominatorThreshold_eq

theorem numerical_square_bound {N : ℕ} (hN : nSquare ≤ N) (hEven : Even N) :
    liuSelbergSquareCount N squareEpsilon (liuSelbergOptimalLambda N squareEpsilon) ≤
      (3.94033 : ℝ)*liuSingularSeries N*N/Real.log N^2+numericalSquareError*N/Real.log N^3 := by
  exact numerical_square_from_main_components N
    ((numerical_square_analytic_cap.trans numerical_pair_power_le_denominator).trans hN) hEven
    (numerical_selberg_denominator_closed hN hEven)
    (numerical_prime_pair_main (numerical_prime_pair_threshold_le_denominator.trans hN))

theorem numerical_triple_bound {N : ℕ} (hN : nSquare ≤ N) (hEven : Even N) :
    correctedChenTriplePenalty N ≤
      (3.94033 : ℝ)*liuSingularSeries N*N/Real.log N^2+
        (numericalTripleErrorCap : ℝ)*N/Real.log N^3 := by
  have hres : tripleResidualThreshold ≤ 3^primePairPowerExponent := by
    unfold tripleResidualThreshold
    apply numerical_log_cutoff_cap
    rw [primePairPowerExponent_eq]
    norm_num
  exact numerical_triple_from_main_components N
    (max_le ((numerical_square_analytic_cap.trans numerical_pair_power_le_denominator).trans hN)
      ((hres.trans numerical_pair_power_le_denominator).trans hN)) hEven
    (numerical_selberg_denominator_closed hN hEven)
    (numerical_prime_pair_main (numerical_prime_pair_threshold_le_denominator.trans hN))

/-- The numerical square/triple branch leaves only the lower-count producer
as a hypothesis in the final Chen endgame. -/
theorem numerical_chen_from_lower (nLower : ℕ)
    (hLower : ∀ N : ℕ, nLower ≤ N → Even N →
      (2.6407 : ℝ)*liuSingularSeries N*N/Real.log N^2 ≤ jurkatRichertWeightedCount N)
    {N : ℕ} (hN : chenCutoff nLower nSquare numericalTripleErrorCap ≤ N) (hEven : Even N) :
    ∃ p q : ℕ, p.Prime ∧ (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q := by
  apply explicit_chen_of_estimates nLower nSquare numericalTripleErrorCap
    (numericalTripleErrorCap : ℝ) le_rfl hLower _ hN hEven
  intro M hM hMeven
  exact numerical_triple_bound hM hMeven

#print axioms numerical_square_bound
#print axioms numerical_triple_bound
#print axioms numerical_chen_from_lower
end ChenEffective
