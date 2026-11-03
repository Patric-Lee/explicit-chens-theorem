import NumericalSquareConstants
import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergEvenAssembly

/-! Numerical remainder and triple assembly. The two finite main-term
premises are retained explicitly until their convergence rates are proved. -/
noncomputable section
namespace ChenEffective
open MathlibNt.SieveTheory
open LiuWeight SingularSeries SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def squareEpsilonDenominator : ℕ := 10000000000
def squareEpsilon : ℝ := 1/(squareEpsilonDenominator : ℝ)
@[irreducible] def squareAnalyticThreshold : ℕ := selbergRemainderThreshold 3 squareEpsilonDenominator

theorem numerical_square_from_main_components (N : ℕ) (hN : squareAnalyticThreshold ≤ N)
    (hEven : Even N)
    (hden : Real.log N/((8+liuM1Delta)*liuSingularSeries N) ≤ liuSelbergDenominator N squareEpsilon)
    (hweight : LiuGenuineLiWeightMainSumBound 2 (0.49254+liuM1Eta) N) :
    liuSelbergSquareCount N squareEpsilon (liuSelbergOptimalLambda N squareEpsilon) ≤
      (3.94033 : ℝ)*liuSingularSeries N*N/Real.log N^2+numericalSquareError*N/Real.log N^3 := by
  have hn := hN
  unfold squareAnalyticThreshold selbergRemainderThreshold at hn
  have hN9 := (logPowerCutoff_nine_le _).trans ((le_max_right _ _).trans hn)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have heHalf : squareEpsilon ≤ (1/2 : ℝ) := by norm_num [squareEpsilon, squareEpsilonDenominator]
  have hR : 1 ≤ paperQSourceCutoff N squareEpsilon := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using Real.one_le_rpow hN1
      (show 0 ≤ 1/4-squareEpsilon/2 by linarith only [heHalf])
  have hadm : LiuSelbergLambdaAdmissible N squareEpsilon (liuSelbergOptimalLambda N squareEpsilon) :=
    ⟨fun _ hd => liuSelbergOptimalLambda_support hd,
      fun d => abs_liuSelbergOptimalLambda_le_one hEven hR⟩
  have hcoef : LiuSelbergCoefficientFactorBound liuM1Delta N squareEpsilon
      (liuSelbergOptimalLambda N squareEpsilon) := by
    unfold LiuSelbergCoefficientFactorBound
    rw [liuSelbergCoefficientFactor_optimalLambda hEven hR]
    exact one_div_liuSelbergDenominator_le (by norm_num [liuM1Delta]) (by omega) hEven hR hden
  have hmain := LiuSelbergMainTermUpperBound.of_componentBounds 2 liuM1Delta liuM1Eta
    (0.49254+liuM1Eta) N squareEpsilon (liuSelbergOptimalLambda N squareEpsilon) hEven hadm
    (by norm_num [liuM1Delta]) (liuSingularSeries_pos N).le
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))) le_rfl liuM1DeltaEta_margin hcoef hweight
  have hr := numerical_selberg_remainder 3 squareEpsilonDenominator N
    (by norm_num [squareEpsilonDenominator]) (by simpa only [squareAnalyticThreshold] using hN)
    (liuSelbergOptimalLambda N squareEpsilon) hadm
  rw [liuSelbergSquareCount_eq_switchedCount,
    liuSelbergSwitchedCount_eq_logarithmicIntegralMainTerm_add_remainder]
  exact add_le_add hmain ((le_abs_self _).trans hr)

theorem numerical_triple_from_main_components (N : ℕ)
    (hN : max squareAnalyticThreshold tripleResidualThreshold ≤ N) (hEven : Even N)
    (hden : Real.log N/((8+liuM1Delta)*liuSingularSeries N) ≤ liuSelbergDenominator N squareEpsilon)
    (hweight : LiuGenuineLiWeightMainSumBound 2 (0.49254+liuM1Eta) N) :
    correctedChenTriplePenalty N ≤
      (3.94033 : ℝ)*liuSingularSeries N*N/Real.log N^2+
        (numericalTripleErrorCap : ℝ)*N/Real.log N^3 := by
  have hs := numerical_square_from_main_components N ((le_max_left _ _).trans hN) hEven hden hweight
  have ht := explicit_triple_from_square ((le_max_right _ _).trans hN) hEven
    squareEpsilon numericalSquareError
    (by norm_num [squareEpsilon, squareEpsilonDenominator])
    (by norm_num [squareEpsilon, squareEpsilonDenominator]) hs
  exact ht.trans (add_le_add le_rfl (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right numerical_square_error_cap (Nat.cast_nonneg N))
    (pow_nonneg (Real.log_nonneg (by
      have hh := tripleResidualThreshold_large.trans ((le_max_right _ _).trans hN)
      exact_mod_cast (show 1 ≤ N by omega))) 3)))

#print axioms numerical_square_from_main_components
#print axioms numerical_triple_from_main_components
end ChenEffective
