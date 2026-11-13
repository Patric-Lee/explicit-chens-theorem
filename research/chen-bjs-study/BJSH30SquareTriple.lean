import BJSH30SquareCap
import BJSH30Denominator
import BJSH30PrimePairMain
import BJSJointBudget
import BJSSelbergLogEnvelope

/-! The relaxed denominator coefficient is propagated through the actual
Selberg square and corrected triple counts. Existing remainder and prime-pair
thresholds remain explicit; no improved small-cutoff distribution is assumed. -/
noncomputable section
namespace ChenEffective.H30
open Real Finset
open MathlibNt.SieveTheory LiuWeight SingularSeries SwitchingPrinciple
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem joint_selberg_square {N : ℕ} (hN : squareAnalyticThreshold ≤ N)
    (hEven : Even N) {K η : ℝ} (hK : 0 < K)
    (hden : log (N:ℝ)/(K*liuSingularSeries N) ≤ liuSelbergDenominator N squareEpsilon)
    (hweight : LiuGenuineLiWeightMainSumBound 2 (0.49254+η) N) :
    liuSelbergSquareCount N squareEpsilon (liuSelbergOptimalLambda N squareEpsilon) ≤
      (K*(0.49254+η))*liuSingularSeries N*N/log (N:ℝ)^2+
        numericalSquareError*N/log (N:ℝ)^3 := by
  have hn := hN
  unfold squareAnalyticThreshold selbergRemainderThreshold at hn
  have hN9 := (logPowerCutoff_nine_le _).trans ((le_max_right _ _).trans hn)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hR : 1 ≤ paperQSourceCutoff N squareEpsilon := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using Real.one_le_rpow hN1
      (show 0 ≤ 1/4-squareEpsilon/2 by norm_num [squareEpsilon,squareEpsilonDenominator])
  have hadm : LiuSelbergLambdaAdmissible N squareEpsilon (liuSelbergOptimalLambda N squareEpsilon) :=
    ⟨fun _ hd => liuSelbergOptimalLambda_support hd,
      fun d => abs_liuSelbergOptimalLambda_le_one hEven hR⟩
  have hcoef : LiuSelbergCoefficientFactorBound (K-8) N squareEpsilon
      (liuSelbergOptimalLambda N squareEpsilon) := by
    unfold LiuSelbergCoefficientFactorBound
    rw [liuSelbergCoefficientFactor_optimalLambda hEven hR]
    have hh := one_div_liuSelbergDenominator_le (delta:=K-8) (by linarith) (by omega)
      hEven hR (by simpa using hden)
    simpa using hh
  have hmain := liuSelbergMainTerm_le_of_componentBounds 2 (K-8) (0.49254+η)
    N squareEpsilon (liuSelbergOptimalLambda N squareEpsilon) hEven hadm
    (by linarith) (liuSingularSeries_pos N).le
    (log_pos (by exact_mod_cast (show 1 < N by omega))) hcoef hweight
  have hr := numerical_selberg_remainder 3 squareEpsilonDenominator N
    (by norm_num [squareEpsilonDenominator]) (by simpa only [squareAnalyticThreshold] using hN)
    (liuSelbergOptimalLambda N squareEpsilon) hadm
  rw [liuSelbergSquareCount_eq_switchedCount,
    liuSelbergSwitchedCount_eq_logarithmicIntegralMainTerm_add_remainder 2]
  exact add_le_add (by simpa only [show (8:ℝ)+(K-8)=K by ring] using hmain)
    (by simpa only [squareEpsilon,numericalSquareError] using (le_abs_self _).trans hr)

theorem joint_triple_from_square {N : ℕ} (hN : tripleResidualThreshold ≤ N)
    (hEven : Even N) {A C : ℝ}
    (hSquare : liuSelbergSquareCount N squareEpsilon (liuSelbergOptimalLambda N squareEpsilon) ≤
      A*liuSingularSeries N*N/log (N:ℝ)^2+C*N/log (N:ℝ)^3) :
    correctedChenTriplePenalty N ≤
      A*liuSingularSeries N*N/log (N:ℝ)^2+(C+19)*N/log (N:ℝ)^3 := by
  have hlarge : 1024 ≤ N := tripleResidualThreshold_large.trans hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hR : 1 ≤ paperQSourceCutoff N squareEpsilon := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using Real.one_le_rpow hN1
      (show 0 ≤ 1/4-squareEpsilon/2 by norm_num [squareEpsilon,squareEpsilonDenominator])
  have hsource := liuSelbergCorrectedSourceTripleCount_le_square_add_QResidual
    (epsilon:=squareEpsilon) hEven hR
  have hc := explicit_triple_complement hN
  have hp := explicit_triple_paper_residual hN squareEpsilon
    (by norm_num [squareEpsilon,squareEpsilonDenominator])
  unfold correctedChenTriplePenalty
  calc
    _ ≤ liuSelbergCorrectedSourceTripleCount N+13*N/log (N:ℝ)^3 := hc
    _ ≤ (liuSelbergSquareCount N squareEpsilon (liuSelbergOptimalLambda N squareEpsilon)+
        liuSelbergCorrectedSourceTripleQResidual N squareEpsilon)+13*N/log (N:ℝ)^3 :=
      add_le_add hsource le_rfl
    _ ≤ (A*liuSingularSeries N*N/log (N:ℝ)^2+C*N/log (N:ℝ)^3+
        6*N/log (N:ℝ)^3)+13*N/log (N:ℝ)^3 :=
      add_le_add (add_le_add hSquare hp) le_rfl
    _ = _ := by ring

theorem joint_triple_closed {N : ℕ} (hN : squareClosedThreshold≤N) (hEven : Even N)
    {K : ℝ} (hK : 82/10≤K) :
    correctedChenTriplePenalty N≤
      (K*(0.49254+1/10000))*liuSingularSeries N*N/log (N:ℝ)^2+
        (numericalTripleErrorCap:ℝ)*N/log (N:ℝ)^3 := by
  have hp := hN
  unfold squareClosedThreshold at hp
  have hL := log_ge_power_three hp
  rw [primePairPowerExponent_eq] at hL
  norm_num only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hL
  have hLog : (10^12:ℝ)≤log (N:ℝ) := by linarith only [hL]
  have hSA : squareAnalyticThreshold≤N := numerical_square_analytic_cap.trans hp
  have hRes : tripleResidualThreshold≤N := by
    apply le_trans _ hN
    unfold squareClosedThreshold tripleResidualThreshold
    apply numerical_log_cutoff_cap
    rw [primePairPowerExponent_eq]
    norm_num
  have hden := expanded_selberg_denominator_of_log
    (show (1000000:ℝ)≤log (N:ℝ) by linarith only [hLog]) hEven hK
  have hs := joint_selberg_square hSA hEven (lt_of_lt_of_le (by norm_num) hK)
    hden (numerical_prime_pair_main hLog)
  have ht := joint_triple_from_square hRes hEven hs
  exact ht.trans (add_le_add le_rfl (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right numerical_square_error_cap (Nat.cast_nonneg N))
    (pow_nonneg (log_natCast_nonneg N) 3)))

#print axioms joint_triple_closed
end ChenEffective.H30

