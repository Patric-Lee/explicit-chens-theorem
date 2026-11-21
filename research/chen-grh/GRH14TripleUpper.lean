import GRH14PrimePairMain
import GRH14TripleConstants
import GRH14TripleBridge

/-! The actual square and corrected triple estimates at the target.
The distribution remainder is supplied by the explicit Pan assembly. -/
noncomputable section
namespace ChenEffective.GRH14
open Real Finset
open MathlibNt.SieveTheory LiuWeight SingularSeries SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem selberg_square_at_target {N : ℕ} (hN : targetCutoff≤N) (hEven : Even N) :
    liuSelbergSquareCount N (1/500:ℝ) (liuSelbergOptimalLambda N (1/500:ℝ)) ≤
      ((80323/10000:ℝ)*0.4971+1/500000)*
        (liuSingularSeries N*N/log (N:ℝ)^2) := by
  let ε : ℝ := 1/500
  let lam := liuSelbergOptimalLambda N ε
  let K : ℝ := 80323/10000
  have hN9 := (logPowerCutoff_nine_le 0).trans (pan_log_cutoff_at_target (k:=0) (by norm_num) hN)
  have hn1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hR : 1≤paperQSourceCutoff N ε := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using Real.one_le_rpow hn1
      (show 0≤1/4-ε/2 by norm_num [ε])
  have hadm : LiuSelbergLambdaAdmissible N ε lam :=
    ⟨fun _ hd => liuSelbergOptimalLambda_support hd,
      fun d => abs_liuSelbergOptimalLambda_le_one hEven hR⟩
  have hcoef : LiuSelbergCoefficientFactorBound (K-8) N ε lam := by
    unfold LiuSelbergCoefficientFactorBound
    rw [liuSelbergCoefficientFactor_optimalLambda hEven hR]
    have hh := one_div_liuSelbergDenominator_le (delta:=K-8)
      (by norm_num [K]) (by omega) hEven hR
      (by simpa [K,ε] using denominator_80323_at_target hN hEven)
    simpa using hh
  have hmain := liuSelbergMainTerm_le_of_componentBounds 2 (K-8) (0.4971:ℝ)
    N ε lam hEven hadm (by norm_num [K]) (liuSingularSeries_pos N).le
    (log_pos (by exact_mod_cast (show 1<N by omega))) hcoef (numerical_prime_pair_main hN)
  have hr := numerical_selberg_remainder hN lam hadm
  have hp := selberg_remainder_paid hN
  rw [liuSelbergSquareCount_eq_switchedCount,
    liuSelbergSwitchedCount_eq_logarithmicIntegralMainTerm_add_remainder 2]
  have hh := add_le_add hmain ((le_abs_self _).trans (hr.trans hp))
  convert hh using 1 <;> dsimp [K,ε,lam] <;> ring

theorem triple_upper {N : ℕ} (hN : targetCutoff≤N) (hEven : Even N) :
    correctedChenTriplePenalty N ≤
      (3.993:ℝ)*(liuSingularSeries N*N/log (N:ℝ)^2) := by
  have hh := triple_of_square_at_target hN hEven
    (ε:=(1/500:ℝ)) (A:=(80323/10000:ℝ)*0.4971+1/500000) (E:=0)
    (by norm_num) (by norm_num) (by simpa using selberg_square_at_target hN hEven)
  have hp := triple_residual_payment hN
  have hm : 0≤liuSingularSeries N*N/log (N:ℝ)^2 :=
    div_nonneg (mul_nonneg (liuSingularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
  nlinarith only [hh,hp,hm]

#print axioms selberg_square_at_target
#print axioms triple_upper
end ChenEffective.GRH14

