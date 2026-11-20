import BJSH30FifthTriple
import BJSH30MertensProduct
import BJSH30MassCap
import BJSH29VariableBudget

/- Derived from BJSH30PanNormalization; checked as new H29 proof source. -/
section
/- Threshold-specialized companion of research/chen-effective/NumericalPanNormalization.lean.
The original producer is retained; all modified numerical statements are rechecked. -/

noncomputable section
namespace ChenEffective.H29
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiuWeight
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def panDivisorConstant : ℝ := (2*Real.exp Real.eulerMascheroniConstant)^3

theorem numerical_pan_full_divisor {N w : ℕ} (hN : H30.mertensProductThreshold 2 ≤ N)
    (hw : w ≤ N) :
    paperQStyleFullDivisorWeightSum N w ≤ panDivisorConstant*Real.log (N : ℝ)^3 := by
  have hprod := H30.numerical_mertens_product (by norm_num : 0 < (2 : ℕ)) hN
  have hNP := (le_max_left _ _).trans hN
  have hN9 := (logPowerCutoff_nine_le _).trans hNP
  have hl0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hP := AnalyticNumberTheory.Mertens.primeProduct_pos N
  have hlow := (abs_le.mp hprod).1
  have hi : (AnalyticNumberTheory.Mertens.primeProduct N)⁻¹ ≤
      2*Real.exp Real.eulerMascheroniConstant*Real.log (N : ℝ) := by
    apply (inv_le_iff_one_le_mul₀ hP).mpr
    norm_num only [Nat.cast_ofNat] at hlow
    nlinarith only [hlow]
  have hh := paperQStyleFullDivisorWeightSum_le_primeProduct_inv_cube N w hw
  rw [MertensTheorem.primeProduct_eq_analyticNumberTheory] at hh
  exact hh.trans ((pow_le_pow_left₀ (by positivity) hi 3).trans_eq
    (by unfold panDivisorConstant; ring))

def panNormalizationConstant : ℝ := 3*panDivisorConstant*|2-2/Real.log 2|
def panCanonicalConstant (A : ℕ) : ℝ := H30.panWeightedConstant A+panNormalizationConstant
@[irreducible] def panCanonicalThreshold (A m : ℕ) : ℕ :=
  max (H30.panSourceThreshold A m) (max (H30.mertensProductThreshold 2) (logPowerCutoff (3*(A+3))))

theorem numerical_pan_canonical (A m N : ℕ) (hm : 0 < m)
    (hN : panCanonicalThreshold A m ≤ N) :
    LiuPaperQCoprimeRBound (liuLogarithmicIntegral 2) N (1/(m : ℝ))
      (A : ℝ) (panCanonicalConstant A) := by
  have hn := hN
  unfold panCanonicalThreshold at hn
  obtain ⟨hNS, hNM, hNP⟩ := (max_le_iff.mp hn).imp_right max_le_iff.mp
  have hN9 := (logPowerCutoff_nine_le _).trans hNP
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hε : 0 ≤ 1/(m : ℝ) := by positivity
  have hmass := sum_liuWeight_Icc_le_three_mul_rpow_two_thirds N
    (liuSourceZ10 N) (liuSourceY3 N) (by omega)
  have hcut := (paperQSourceCutoff_le_floor_cuberoot N (1/(m : ℝ)) (by omega) hε).trans
    (liuSourceY3_le N (by omega))
  have hdiv := numerical_pan_full_divisor hNM hcut
  have hmass0 : 0 ≤ ∑ a ∈ Icc 1 N, liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a := by
    apply sum_nonneg
    intro a _
    exact liuWeight_nonneg _ _ _ _
  have hfactor : 0 ≤ paperQStyleFullDivisorWeightSum N (paperQSourceCutoff N (1/(m : ℝ))) := by
    unfold paperQStyleFullDivisorWeightSum
    positivity
  have hnorm := liuPaperQSourceCoprimeDistributionMajorant_li_normalization_le
    2 (2/Real.log 2) N (1/(m : ℝ))
  have hloss : |2-2/Real.log 2| *
      (∑ a ∈ Icc 1 N, liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a)*
      paperQStyleFullDivisorWeightSum N (paperQSourceCutoff N (1/(m : ℝ))) ≤
        panNormalizationConstant*N/Real.log (N : ℝ)^A := by
    have hp := log_pow_le_rpow_inv_explicit (k := A+3) (m := 3)
      (by norm_num) (le_refl _) hNP
    norm_num only [Nat.cast_ofNat] at hp
    have hscale : (N : ℝ)^(2/3 : ℝ)*Real.log (N : ℝ)^3 ≤ N/Real.log (N : ℝ)^A := by
      apply (le_div_iff₀ (pow_pos hlog A)).mpr
      calc
        _ = (N : ℝ)^(2/3 : ℝ)*Real.log (N : ℝ)^(A+3) := by rw [pow_add]; ring
        _ ≤ (N : ℝ)^(2/3 : ℝ)*(N : ℝ)^(1/3 : ℝ) := by gcongr
        _ = _ := by rw [← Real.rpow_add hN0]; norm_num
    calc
      _ ≤ |2-2/Real.log 2| *(3*(N : ℝ)^(2/3 : ℝ))*(panDivisorConstant*Real.log (N : ℝ)^3) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hmass (abs_nonneg _)) hdiv hfactor
          (by positivity)
      _ = panNormalizationConstant*((N : ℝ)^(2/3 : ℝ)*Real.log (N : ℝ)^3) := by
        unfold panNormalizationConstant; ring
      _ ≤ panNormalizationConstant*(N/Real.log (N : ℝ)^A) := by
        apply mul_le_mul_of_nonneg_left hscale
        unfold panNormalizationConstant panDivisorConstant
        positivity
      _ = _ := by ring
  unfold LiuPaperQCoprimeRBound
  rw [Real.rpow_natCast]
  have hsource := H30.numerical_pan_source A m N hm hNS
  unfold LiuPaperQCoprimeRBound at hsource
  rw [Real.rpow_natCast] at hsource
  exact hnorm.trans ((add_le_add hsource hloss).trans_eq (by unfold panCanonicalConstant; ring))

#print axioms numerical_pan_canonical
end ChenEffective.H29

end
end

/- Derived from BJSH30SelbergRemainder; checked as new H29 proof source. -/
section
/- Threshold-specialized companion of research/chen-effective/NumericalSelbergRemainder.lean.
The original producer is retained; all modified numerical statements are rechecked. -/

noncomputable section
namespace ChenEffective.H29
open MathlibNt.SieveTheory.LiuWeight
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def selbergRemainderConstant (A : ℕ) : ℝ :=
  panCanonicalConstant A+1920*liuLogarithmicIntegralUpperConstant 2
@[irreducible] def selbergRemainderThreshold (A m : ℕ) : ℕ :=
  max (panCanonicalThreshold A m) (logPowerCutoff (10*(A+6)))

theorem numerical_selberg_remainder (A m N : ℕ) (hm : 0 < m)
    (hN : selbergRemainderThreshold A m ≤ N) (lam : ℕ → ℝ)
    (hlam : LiuSelbergLambdaAdmissible N (1/(m : ℝ)) lam) :
    |liuSelbergRemainder (liuLogarithmicIntegral 2) N (1/(m : ℝ)) lam| ≤
      selbergRemainderConstant A*N/Real.log (N : ℝ)^A := by
  have hn := hN
  unfold selbergRemainderThreshold at hn
  obtain ⟨hNC, hNP⟩ := max_le_iff.mp hn
  have hN9 := (logPowerCutoff_nine_le _).trans hNP
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL := log_one_le_of_eight_le (by omega : 8 ≤ N)
  have hl0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL
  have hε : 0 ≤ 1/(m : ℝ) := by positivity
  have hcop := numerical_pan_canonical A m N hm hNC
  unfold LiuPaperQCoprimeRBound at hcop
  rw [Real.rpow_natCast] at hcop
  have hp := log_pow_le_rpow_inv_explicit (k := A+6) (m := 10)
    (by norm_num) (le_refl _) hNP
  norm_num only [Nat.cast_ofNat] at hp
  have hscale : (N : ℝ)^(9/10 : ℝ)*Real.log (N : ℝ)^6 ≤ N/Real.log (N : ℝ)^A := by
    apply (le_div_iff₀ (pow_pos hl0 A)).mpr
    calc
      _ = (N : ℝ)^(9/10 : ℝ)*Real.log (N : ℝ)^(A+6) := by rw [pow_add]; ring
      _ ≤ (N : ℝ)^(9/10 : ℝ)*(N : ℝ)^(1/10 : ℝ) := by gcongr
      _ = _ := by rw [← Real.rpow_add hN0]; norm_num
  have hr := H30.numerical_pan_r1 2 N (1/(m : ℝ)) hN9 hε
  have hpaid : liuPaperQSourceR1Majorant (liuLogarithmicIntegral 2) N (1/(m : ℝ)) ≤
      1920*liuLogarithmicIntegralUpperConstant 2*N/Real.log (N : ℝ)^A := by
    have hC := liuLogarithmicIntegralUpperConstant_nonneg 2
    calc
      _ ≤ 30*liuLogarithmicIntegralUpperConstant 2*(N : ℝ)^(9/10 : ℝ)*
          (1+Real.log (N : ℝ))^6 := hr
      _ ≤ 30*liuLogarithmicIntegralUpperConstant 2*(N : ℝ)^(9/10 : ℝ)*
          (2*Real.log (N : ℝ))^6 := by
        gcongr
        linarith only [hL]
      _ = (1920*liuLogarithmicIntegralUpperConstant 2)*
          ((N : ℝ)^(9/10 : ℝ)*Real.log (N : ℝ)^6) := by ring
      _ ≤ (1920*liuLogarithmicIntegralUpperConstant 2)*(N/Real.log (N : ℝ)^A) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = _ := by ring
  exact (abs_liuSelbergRemainder_le_fullDistributionMajorant _ N _ lam (by omega) hlam).trans
    ((liuPaperQSourceFullDistributionMajorant_le_coprime_add_r1 _ N _ (by omega) hε).trans
      ((add_le_add hcop hpaid).trans_eq (by unfold selbergRemainderConstant; ring)))

#print axioms numerical_selberg_remainder
end ChenEffective.H29

end
end

/- Derived from new cutoff and inherited constant cap; checked as new H29 proof source. -/
section
noncomputable section
namespace ChenEffective.H29
open Real
set_option maxHeartbeats 3000000
private opaque analyticCertificate : {n : ℕ // n=3*10^12} := ⟨3*10^12,rfl⟩
def primePairPowerExponent : ℕ := analyticCertificate.1
theorem primePairPowerExponent_eq : primePairPowerExponent=3*10^12 := analyticCertificate.2
theorem cutoff_lt_double_exp_29 :
    ((3^(3*10^12):ℕ):ℝ)<exp (exp (29:ℝ)) := by
  have he : (2718/1000:ℝ)≤exp 1 := by linarith only [exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) he 29
  rw [← exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat,mul_one] at hp
  have hexp : (3600000000000:ℝ)<exp 29 := by nlinarith only [hp]
  have hlog : log (((3^(3*10^12):ℕ):ℝ))<exp 29 := by
    rw [Nat.cast_pow,log_pow]
    norm_num only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    nlinarith only [log_three_cap,hexp]
  apply (log_lt_log_iff (by positivity : (0:ℝ)<((3^(3*10^12):ℕ):ℝ))
    (exp_pos (exp (29:ℝ)))).mp
  rw [log_exp]
  exact hlog
@[irreducible] def squareClosedThreshold : ℕ := 3^primePairPowerExponent
def fifthSquareError : ℝ := selbergRemainderConstant 5
def fifthSquareErrorCap : ℕ := 10^34
theorem fifth_square_error_cap : fifthSquareError+19 ≤ fifthSquareErrorCap := by
  simpa only [fifthSquareError,fifthSquareErrorCap,selbergRemainderConstant,panCanonicalConstant,
    panNormalizationConstant,panDivisorConstant,H30.fifthSquareError,H30.fifthSquareErrorCap,
    H30.selbergRemainderConstant,H30.panCanonicalConstant,H30.panNormalizationConstant,
    H30.panDivisorConstant] using H30.fifth_square_error_cap
end ChenEffective.H29
end

end

/- Derived from BJSH30FifthCap; checked as new H29 proof source. -/
section
noncomputable section
namespace ChenEffective.H29
open NumericalPanHigh
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] logPowerCutoff
@[irreducible] def fifthAnalyticThreshold : ℕ := selbergRemainderThreshold 5 H30.squareEpsilonDenominator

private theorem fifth_mertens_power_cap {r E : ℕ}
    (hlog : 16*(2+1)^2 ≤ E) (hpow : 6*r+1 ≤ E) :
    H30.mertensProductThreshold r ≤ 3^E := by
  unfold H30.mertensProductThreshold
  exact max_le (H30.numerical_log_cutoff_cap _ _ hlog)
    (Nat.pow_le_pow_right (by norm_num) hpow)

theorem fifth_analytic_cap : fifthAnalyticThreshold ≤ 3^primePairPowerExponent := by
  have hprefix : H30.panPrimePrefixThreshold 72 ≤ 3^(primePairPowerExponent/4) := by
    unfold H30.panPrimePrefixThreshold primitiveNumericalThreshold
    apply max_le
    all_goals
      apply H30.numerical_log_cutoff_cap
      rw [primePairPowerExponent_eq]
      norm_num
  have hmove : H30.panMovingPrimeThreshold 38 72 ≤ 3^primePairPowerExponent := by
    unfold H30.panMovingPrimeThreshold
    apply H30.numerical_quotient_cutoff_cap _ _ _ hprefix
    all_goals rw [primePairPowerExponent_eq]; norm_num
  have hlow : H30.panLowThreshold 32 38 ≤ 3^primePairPowerExponent := by
    unfold H30.panLowThreshold
    apply max_le
    · exact H30.numerical_small_power_cap 9 primePairPowerExponent (by norm_num)
        (by rw [primePairPowerExponent_eq]; norm_num)
    · apply max_le hmove
      unfold panBudgetThreshold
      apply H30.numerical_log_cutoff_cap
      rw [primePairPowerExponent_eq]
      norm_num
  have hreal : H30.panRealDivPNTThreshold 34 ≤ 3^(primePairPowerExponent/4) := by
    unfold H30.panRealDivPNTThreshold H30.panPrimePNTThreshold numericalBVThreshold bvThreshold
      highBVThreshold primitiveNumericalThreshold principalNumericalThreshold
    apply max_le
    · exact H30.numerical_small_power_cap 2 (primePairPowerExponent/4) (by norm_num)
        (by rw [primePairPowerExponent_eq]; norm_num)
    · repeat' apply max_le
      all_goals
        apply H30.numerical_log_cutoff_cap
        rw [primePairPowerExponent_eq]
        norm_num [highBVConductorExponent,highBVExponent]
  have hpMove : H30.panMovingPNTThreshold 34 ≤ 3^primePairPowerExponent := by
    unfold H30.panMovingPNTThreshold
    apply H30.numerical_quotient_cutoff_cap _ _ _ hreal
    all_goals rw [primePairPowerExponent_eq]; norm_num
  have hprincipal : H30.panPrincipalThreshold 32 ≤ 3^primePairPowerExponent := by
    unfold H30.panPrincipalThreshold
    apply max_le hpMove
    unfold panBudgetThreshold
    apply H30.numerical_log_cutoff_cap
    rw [primePairPowerExponent_eq]
    norm_num
  have hledger : H30.panLedgerThreshold 32 ≤ 3^primePairPowerExponent := by
    unfold H30.panLedgerThreshold
    apply max_le hlow
    apply max_le
    · unfold panHighThreshold
      apply H30.numerical_log_cutoff_cap
      rw [primePairPowerExponent_eq]
      norm_num
    · apply H30.numerical_log_cutoff_cap
      rw [primePairPowerExponent_eq]
      norm_num
  have hweighted : H30.panWeightedThreshold 5 ≤ 3^primePairPowerExponent := by
    unfold H30.panWeightedThreshold H30.panUnweightedThreshold H30.panWeightedSaving
    exact max_le hledger hprincipal
  have hsource : H30.panSourceThreshold 5 H30.squareEpsilonDenominator ≤ 3^primePairPowerExponent := by
    unfold H30.panSourceThreshold
    apply max_le hweighted
    apply max_le
    · unfold H30.panSourceSupportThreshold
      apply max_le
      · calc
          _ ≤ (3 : ℕ)^20 := Nat.pow_le_pow_left (by norm_num : (2 : ℕ) ≤ 3) 20
          _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by rw [primePairPowerExponent_eq]; norm_num)
      · apply H30.numerical_log_cutoff_cap
        rw [primePairPowerExponent_eq]
        norm_num [H30.panWeightedCutoff,H30.panWeightedSaving]
    · apply H30.numerical_log_cutoff_cap
      rw [primePairPowerExponent_eq]
      norm_num [H30.squareEpsilonDenominator,H30.panWeightedCutoff,H30.panWeightedSaving]
  have hMertens : H30.mertensProductThreshold 2 ≤ 3^primePairPowerExponent :=
    fifth_mertens_power_cap
      (by rw [primePairPowerExponent_eq]; norm_num)
      (by rw [primePairPowerExponent_eq]; norm_num)
  unfold fifthAnalyticThreshold selbergRemainderThreshold panCanonicalThreshold
  apply max_le
  · apply max_le hsource
    apply max_le hMertens
    apply H30.numerical_log_cutoff_cap
    rw [primePairPowerExponent_eq]
    norm_num
  · apply H30.numerical_log_cutoff_cap
    rw [primePairPowerExponent_eq]
    norm_num

#print axioms fifth_analytic_cap
end ChenEffective.H29

end
end

/- Derived from BJSH30FifthTriple; checked as new H29 proof source. -/
section

/-! The relaxed denominator coefficient is propagated through the actual
Selberg square and corrected triple counts. Existing remainder and prime-pair
thresholds remain explicit; no improved small-cutoff distribution is assumed. -/
noncomputable section
namespace ChenEffective.H29
open Real Finset
open MathlibNt.SieveTheory LiuWeight SingularSeries SwitchingPrinciple
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem fifth_selberg_square {N : ℕ} (hN : fifthAnalyticThreshold ≤ N)
    (hEven : Even N) {K η : ℝ} (hK : 0 < K)
    (hden : log (N:ℝ)/(K*liuSingularSeries N) ≤ liuSelbergDenominator N H30.squareEpsilon)
    (hweight : LiuGenuineLiWeightMainSumBound 2 (0.49254+η) N) :
    liuSelbergSquareCount N H30.squareEpsilon (liuSelbergOptimalLambda N H30.squareEpsilon) ≤
      (K*(0.49254+η))*liuSingularSeries N*N/log (N:ℝ)^2+
        fifthSquareError*N/log (N:ℝ)^5 := by
  have hn := hN
  unfold fifthAnalyticThreshold selbergRemainderThreshold at hn
  have hN9 := (logPowerCutoff_nine_le _).trans ((le_max_right _ _).trans hn)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hR : 1 ≤ paperQSourceCutoff N H30.squareEpsilon := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using Real.one_le_rpow hN1
      (show 0 ≤ 1/4-H30.squareEpsilon/2 by norm_num [H30.squareEpsilon,H30.squareEpsilonDenominator])
  have hadm : LiuSelbergLambdaAdmissible N H30.squareEpsilon (liuSelbergOptimalLambda N H30.squareEpsilon) :=
    ⟨fun _ hd => liuSelbergOptimalLambda_support hd,
      fun d => abs_liuSelbergOptimalLambda_le_one hEven hR⟩
  have hcoef : LiuSelbergCoefficientFactorBound (K-8) N H30.squareEpsilon
      (liuSelbergOptimalLambda N H30.squareEpsilon) := by
    unfold LiuSelbergCoefficientFactorBound
    rw [liuSelbergCoefficientFactor_optimalLambda hEven hR]
    have hh := one_div_liuSelbergDenominator_le (delta:=K-8) (by linarith) (by omega)
      hEven hR (by simpa using hden)
    simpa using hh
  have hmain := liuSelbergMainTerm_le_of_componentBounds 2 (K-8) (0.49254+η)
    N H30.squareEpsilon (liuSelbergOptimalLambda N H30.squareEpsilon) hEven hadm
    (by linarith) (liuSingularSeries_pos N).le
    (log_pos (by exact_mod_cast (show 1 < N by omega))) hcoef hweight
  have hr := numerical_selberg_remainder 5 H30.squareEpsilonDenominator N
    (by norm_num [H30.squareEpsilonDenominator]) (by simpa only [fifthAnalyticThreshold] using hN)
    (liuSelbergOptimalLambda N H30.squareEpsilon) hadm
  rw [liuSelbergSquareCount_eq_switchedCount,
    liuSelbergSwitchedCount_eq_logarithmicIntegralMainTerm_add_remainder 2]
  exact add_le_add (by simpa only [show (8:ℝ)+(K-8)=K by ring] using hmain)
    (by simpa only [H30.squareEpsilon,fifthSquareError] using (le_abs_self _).trans hr)

theorem fifth_triple_from_square {N : ℕ} (hN : tripleResidualThreshold ≤ N)
    (hEven : Even N) {A C : ℝ}
    (hSquare : liuSelbergSquareCount N H30.squareEpsilon (liuSelbergOptimalLambda N H30.squareEpsilon) ≤
      A*liuSingularSeries N*N/log (N:ℝ)^2+C*N/log (N:ℝ)^5) :
    correctedChenTriplePenalty N ≤
      A*liuSingularSeries N*N/log (N:ℝ)^2+C*N/log (N:ℝ)^5+19*N/log (N:ℝ)^3 := by
  have hlarge : 1024 ≤ N := tripleResidualThreshold_large.trans hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hR : 1 ≤ paperQSourceCutoff N H30.squareEpsilon := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using Real.one_le_rpow hN1
      (show 0 ≤ 1/4-H30.squareEpsilon/2 by norm_num [H30.squareEpsilon,H30.squareEpsilonDenominator])
  have hsource := liuSelbergCorrectedSourceTripleCount_le_square_add_QResidual
    (epsilon:=H30.squareEpsilon) hEven hR
  have hc := explicit_triple_complement hN
  have hp := explicit_triple_paper_residual hN H30.squareEpsilon
    (by norm_num [H30.squareEpsilon,H30.squareEpsilonDenominator])
  unfold correctedChenTriplePenalty
  calc
    _ ≤ liuSelbergCorrectedSourceTripleCount N+13*N/log (N:ℝ)^3 := hc
    _ ≤ (liuSelbergSquareCount N H30.squareEpsilon (liuSelbergOptimalLambda N H30.squareEpsilon)+
        liuSelbergCorrectedSourceTripleQResidual N H30.squareEpsilon)+13*N/log (N:ℝ)^3 :=
      add_le_add hsource le_rfl
    _ ≤ (A*liuSingularSeries N*N/log (N:ℝ)^2+C*N/log (N:ℝ)^5+
        6*N/log (N:ℝ)^3)+13*N/log (N:ℝ)^3 :=
      add_le_add (add_le_add hSquare hp) le_rfl
    _ = _ := by ring

/-- Paying the actual fifth-order square remainder and both third-order
complements separately avoids inflating them to a common third-order constant. -/
theorem fifth_error_payment {N : ℕ} (hL : (3*10^12 : ℝ) ≤ log (N:ℝ)) :
    fifthSquareError*N/log (N:ℝ)^5+19*N/log (N:ℝ)^3 ≤
      (1/1000 : ℝ)*(liuSingularSeries N*N/log (N:ℝ)^2) := by
  have hl : 0 < log (N:ℝ) := lt_of_lt_of_le (by norm_num) hL
  have hs := half_le_liuSingularSeries N
  have hc : fifthSquareError ≤ (log (N:ℝ))^3/2500 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3*10^12) hL 3
    have he := fifth_square_error_cap
    norm_num [fifthSquareErrorCap] at he
    nlinarith only [hp,he]
  have hr : (19 : ℝ) ≤ log (N:ℝ)/10000 := by linarith only [hL]
  have h1 : fifthSquareError/(log (N:ℝ))^3 ≤ 1/2500 :=
    (div_le_iff₀ (pow_pos hl 3)).mpr (by linarith only [hc])
  have h2 : (19:ℝ)/log (N:ℝ) ≤ 1/10000 :=
    (div_le_iff₀ hl).mpr (by linarith only [hr])
  have hcoeff : fifthSquareError/(log (N:ℝ))^3+19/log (N:ℝ) ≤
      (1/1000 : ℝ)*liuSingularSeries N := by linarith only [h1,h2,hs]
  have hp := mul_le_mul_of_nonneg_right hcoeff
    (div_nonneg (Nat.cast_nonneg N) (sq_nonneg (log (N:ℝ))))
  convert hp using 1 <;> first | rfl | (field_simp [hl.ne'])

theorem fifth_triple_variable {N : ℕ} (hN : squareClosedThreshold ≤ N) (hEven : Even N)
    {K : ℝ} (hK : 82/10 ≤ K) :
    correctedChenTriplePenalty N ≤
      (K*(0.49254+1/10000)+tripleErrorEnvelope fifthSquareError (log (N:ℝ)))*
        (liuSingularSeries N*N/log (N:ℝ)^2) := by
  have hp := hN
  unfold squareClosedThreshold at hp
  have hL := log_ge_power_three hp
  rw [primePairPowerExponent_eq] at hL
  norm_num only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hL
  have hLog : (10^12:ℝ)≤log (N:ℝ) := by linarith only [hL]
  have hSA : fifthAnalyticThreshold≤N := fifth_analytic_cap.trans hp
  have hRes : tripleResidualThreshold≤N := by
    apply le_trans _ hN
    unfold squareClosedThreshold tripleResidualThreshold
    apply H30.numerical_log_cutoff_cap
    rw [primePairPowerExponent_eq]
    norm_num
  have hden := H30.expanded_selberg_denominator_of_log
    (show (1000000:ℝ)≤log (N:ℝ) by linarith only [hLog]) hEven hK
  have hs := fifth_selberg_square hSA hEven (lt_of_lt_of_le (by norm_num) hK)
    hden (H30.numerical_prime_pair_main hLog)
  have ht := fifth_triple_from_square hRes hEven hs
  have hC : 0≤fifthSquareError := by
    unfold fifthSquareError selbergRemainderConstant panCanonicalConstant
      panNormalizationConstant panDivisorConstant H30.panWeightedConstant
    have := liuLogarithmicIntegralUpperConstant_nonneg 2
    positivity
  have he := variable_triple_error_payment hC (Nat.cast_nonneg N)
    (show 0<log (N:ℝ) by linarith only [hLog]) (half_le_liuSingularSeries N)
  calc
    _ ≤ K*(0.49254+1/10000)*liuSingularSeries N*N/log (N:ℝ)^2+
        (fifthSquareError*N/log (N:ℝ)^5+19*N/log (N:ℝ)^3) := by linarith only [ht]
    _ ≤ K*(0.49254+1/10000)*liuSingularSeries N*N/log (N:ℝ)^2+
        tripleErrorEnvelope fifthSquareError (log (N:ℝ))*
          (liuSingularSeries N*N/log (N:ℝ)^2) := add_le_add le_rfl he
    _ = _ := by ring

theorem fifth_triple_closed {N : ℕ} (hN : squareClosedThreshold ≤ N) (hEven : Even N)
    {K : ℝ} (hK : 82/10 ≤ K) :
    correctedChenTriplePenalty N ≤
      (K*(0.49254+1/10000)+1/1000)*(liuSingularSeries N*N/log (N:ℝ)^2) := by
  have hp := hN
  unfold squareClosedThreshold at hp
  have hL := log_ge_power_three hp
  rw [primePairPowerExponent_eq] at hL
  norm_num only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hL
  have hLog : (10^12:ℝ) ≤ log (N:ℝ) := by linarith only [hL]
  have hSA : fifthAnalyticThreshold ≤ N := fifth_analytic_cap.trans hp
  have hRes : tripleResidualThreshold ≤ N := by
    apply le_trans _ hN
    unfold squareClosedThreshold tripleResidualThreshold
    apply H30.numerical_log_cutoff_cap
    rw [primePairPowerExponent_eq]
    norm_num
  have hden := H30.expanded_selberg_denominator_of_log
    (show (1000000:ℝ) ≤ log (N:ℝ) by linarith only [hLog]) hEven hK
  have hs := fifth_selberg_square hSA hEven (lt_of_lt_of_le (by norm_num) hK)
    hden (H30.numerical_prime_pair_main hLog)
  have ht := fifth_triple_from_square hRes hEven hs
  have he := fifth_error_payment (N:=N) (by norm_num at *; exact hL)
  calc
    _ ≤ K*(0.49254+1/10000)*liuSingularSeries N*N/log (N:ℝ)^2+
        (fifthSquareError*N/log (N:ℝ)^5+19*N/log (N:ℝ)^3) := by
      linarith only [ht]
    _ ≤ K*(0.49254+1/10000)*liuSingularSeries N*N/log (N:ℝ)^2+
        (1/1000 : ℝ)*(liuSingularSeries N*N/log (N:ℝ)^2) := add_le_add_right he _
    _ = _ := by ring

/-- Only the lower counting estimate remains as an input here: all upper-count
estimates, including the Q residual and complement, have been discharged. -/
theorem chen_of_lower {N : ℕ} (hN : squareClosedThreshold ≤ N) (hEven : Even N)
    (hlower : (2.02575 : ℝ)*(liuSingularSeries N*N/log (N:ℝ)^2) ≤
      jurkatRichertWeightedCount N) :
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q := by
  have hN9 : 9 ≤ N := by
    apply le_trans _ hN
    unfold squareClosedThreshold
    exact (show (3:ℕ)^2 ≤ 3^primePairPowerExponent from
      Nat.pow_le_pow_right (by norm_num) (by rw [primePairPowerExponent_eq]; norm_num))
  have hp := hN
  unfold squareClosedThreshold at hp
  have hL := log_ge_power_three hp
  rw [primePairPowerExponent_eq] at hL
  norm_num only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hL
  have hc : fifthSquareError≤10^34 := by
    have hh := fifth_square_error_cap
    norm_num only [fifthSquareErrorCap] at hh
    linarith only [hh]
  have herr := variable_triple_envelope_cap hc (by norm_num at hL ⊢; exact hL)
  let b := variableChenBudget (1/20) (113/100) (1/20000) (82/10) (1/10000)
    fifthSquareError (log (N:ℝ))
  apply chen_budget_existence b hN9
  · dsimp only [b]
    rw [variable_margin]
    nlinarith only [herr]
  · convert hlower using 1 <;> norm_num [b,variableChenBudget,ChenBudget.weighted]
  · simpa only [b,variableChenBudget] using fifth_triple_variable hN hEven (K:=82/10) le_rfl

#print axioms fifth_triple_closed
#print axioms chen_of_lower
end ChenEffective.H29






end
end

/- Derived from BJSH30MassCap; checked as new H29 proof source. -/
section

noncomputable section
namespace ChenEffective.H29
open MathlibNt.SieveTheory SwitchingPrinciple
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 512

theorem source_product_cap {r : ℕ} (hr : r≤10^10) : H30.chenProductThreshold r≤ squareClosedThreshold := by
  have hM : H30.mertensProductThreshold r≤3^(primePairPowerExponent/20) := by
    unfold H30.mertensProductThreshold
    apply max_le
    · apply numerical_log_cutoff_cap
      rw [primePairPowerExponent_eq]
      norm_num
    · apply Nat.pow_le_pow_right (by decide)
      rw [primePairPowerExponent_eq]
      omega
  have h2 : 2≤(3:ℕ)^(primePairPowerExponent/20) :=
    (by decide : 2≤(3:ℕ)^1).trans (Nat.pow_le_pow_right (by decide) (by rw [primePairPowerExponent_eq]; norm_num))
  have hh : (3:ℕ)^(primePairPowerExponent/20)+1≤((3:ℕ)^(primePairPowerExponent/20))^2 := by nlinarith only [h2]
  unfold H30.chenProductThreshold squareClosedThreshold
  calc
    _ ≤ ((3:ℕ)^(primePairPowerExponent/20)+1)^10 := Nat.pow_le_pow_left (Nat.add_le_add_right hM 1) 10
    _ ≤ (((3:ℕ)^(primePairPowerExponent/20))^2)^10 := Nat.pow_le_pow_left hh 10
    _ = 3^((primePairPowerExponent/20)*20) := by rw [← pow_mul,← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.div_mul_le_self _ _)

theorem small_tenth_power_cap {a : ℕ} (ha : a≤3^30) : a^10≤ squareClosedThreshold := by
  unfold squareClosedThreshold
  calc
    _ ≤ ((3:ℕ)^30)^10 := Nat.pow_le_pow_left ha 10
    _ = 3^300 := by rw [← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by rw [primePairPowerExponent_eq]; norm_num)

theorem source_mass_caps {r : ℕ} (hr : r≤10^10) :
    H30.sourceMassThreshold r≤ squareClosedThreshold ∧ H30.sourceUpperMassThreshold r≤ squareClosedThreshold := by
  have hsmall : (2:ℕ)^110+1≤ squareClosedThreshold := by
    unfold squareClosedThreshold
    exact (by norm_num : (2:ℕ)^110+1≤3^100).trans
      (Nat.pow_le_pow_right (by decide) (by rw [primePairPowerExponent_eq]; norm_num))
  have hsing : singularNormalizationThreshold r≤ squareClosedThreshold := by
    unfold singularNormalizationThreshold
    apply max_le hsmall
    apply small_tenth_power_cap
    nlinarith only [hr]
  constructor
  · exact max_le (source_product_cap hr) hsing
  · unfold H30.sourceUpperMassThreshold
    apply max_le (source_product_cap hr)
    apply max_le (small_tenth_power_cap (by nlinarith only [hr]))
    apply max_le
    · unfold squareClosedThreshold
      apply Nat.pow_le_pow_right (by decide)
      rw [primePairPowerExponent_eq]
      omega
    · unfold squareClosedThreshold
      apply numerical_log_cutoff_cap
      rw [primePairPowerExponent_eq]
      norm_num

theorem source_mass_at_closed_threshold {r N : ℕ} (hr : 0<r) (hrcap : r≤10^10)
    (hN : squareClosedThreshold≤N) (hEven : Even N) :
    (20*Real.exp (-Real.eulerMascheroniConstant)-40/(r:ℝ))*
      (SingularSeries.liuSingularSeries N*N/Real.log (N:ℝ)^2)≤
      (jurkatRichertSourceBoundingSieve N).totalMass*
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceBoundingSieve N) ∧
    (jurkatRichertSourceBoundingSieve N).totalMass*
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceBoundingSieve N)≤
      (jurkatRichertMertensFactor+300/(r:ℝ))*
        (SingularSeries.liuSingularSeries N*N/Real.log (N:ℝ)^2) := by
  have hc := source_mass_caps hrcap
  constructor
  · convert H30.numerical_source_mass_lower hr (hc.1.trans hN) hEven using 1
    ring
  · exact H30.numerical_source_mass_upper hr (hc.2.trans hN) hEven

#print axioms source_mass_at_closed_threshold
end ChenEffective.H29

end
end
