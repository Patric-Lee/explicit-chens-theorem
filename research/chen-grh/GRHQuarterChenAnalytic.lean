import GRHQuarterChenPan

/- Component: GRHQuarterChenTripleConstants -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real
open MathlibNt.SieveTheory LiuWeight
open NumericalPanHigh
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem selberg_remainder_constant_cap : selbergRemainderConstant 5≤(30000000:ℝ) := by
  exact GRHJoint.selberg_constant_cap

theorem selberg_remainder_paid {N : ℕ} (hN : targetCutoff≤ N) :
    selbergRemainderConstant 5*N/log (N:ℝ)^5 ≤
      (1/1000:ℝ)*(SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2) := by
  have hL := target_log_lower hN
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hs := half_le_liuSingularSeries N
  have hc : selbergRemainderConstant 5/log (N:ℝ)^3 ≤
      (1/1000:ℝ)*SingularSeries.liuSingularSeries N := by
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤130690) hL 3
    apply (div_le_iff₀ (pow_pos hl 3)).mpr
    have hh := mul_le_mul hs hp (by norm_num : (0:ℝ)≤130690^3)
      (SingularSeries.liuSingularSeries_pos N).le
    nlinarith only [hh,selberg_remainder_constant_cap]
  have hh := mul_le_mul_of_nonneg_right hc
    (show 0≤(N:ℝ)/log (N:ℝ)^2 by positivity)
  convert hh using 1 <;> field_simp [hl.ne']

#print axioms selberg_remainder_paid
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenScalarBudget -/
/-! Conditional adapter for actual Chen counts at the H<14 target. The
analytic lower and complete triple inequalities remain explicit premises. -/
noncomputable section
open Real
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
namespace ChenEffective.GRHQuarterChen
/-- These are bounds on actual counts, not numerical sieve axioms. -/
theorem representation_of_target_counts {N : ℕ} (hN : targetCutoff ≤ N)
    (hlower : (2.00825 : ℝ)*(SingularSeries.liuSingularSeries N*N/log (N : ℝ)^2) ≤
      MathlibNt.SieveTheory.SwitchingPrinciple.jurkatRichertWeightedCount N)
    (htriple : MathlibNt.SieveTheory.SwitchingPrinciple.correctedChenTriplePenalty N ≤
      ((81/10 : ℝ)*(0.49254+1/10000)+1/1000)*
        (SingularSeries.liuSingularSeries N*N/log (N : ℝ)^2)) :
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q := by
  have hN9 : 9 ≤ N := by
    have hE : 2 ≤ targetExponent := by rw [targetExponent_eq]; norm_num
    exact (show (9 : ℕ)=3^2 by norm_num).le.trans
      ((Nat.pow_le_pow_right (by norm_num : 1 ≤ (3 : ℕ)) hE).trans hN)
  have hM : 0 < SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2 := by
    exact div_pos (mul_pos (SingularSeries.liuSingularSeries_pos N)
      (by exact_mod_cast (show 0 < N by omega)))
      (pow_pos (log_pos (by exact_mod_cast (show 1 < N by omega))) 2)
  have hb := corrected_counting_bridge_public_of_nine_le hN9
  rw [correctedChenKeyCount_eq_jurkatRichertWeightedCount_sub_triple] at hb
  have hcard : 0 < (chenGoodRepresentations N).card := by
    exact_mod_cast (show (0:ℝ) < ((chenGoodRepresentations N).card:ℝ) by
      nlinarith only [hb,hlower,htriple,hM])
  obtain ⟨p,hp⟩ := Finset.card_pos.mp hcard
  simp only [chenGoodRepresentations,Finset.mem_filter,Finset.mem_range] at hp
  exact ⟨p,N-p,hp.2.1,MathlibNt.ChensTheorem.semiprime_iff.mp
    ⟨hp.2.2.1,hp.2.2.2⟩,by omega⟩

#print axioms representation_of_target_counts
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenSelbergBudget -/
/-! The actual Selberg denominator at the H<14 target, uniformly in the
sieving radius parameter. These statements are unconditional. They remove
the restriction to the old fixed epsilon; they do not assert the complete
triple count, whose off-diagonal and prime-pair errors still need work. -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Finset
open MathlibNt.SieveTheory LiuWeight SingularSeries
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
theorem normalized_error {N R : ℕ} {ε : ℝ} (hε : ε ≤ 1/1000)
    (hN : 0<N) (hL : (130690:ℝ)≤ log (N:ℝ)) (hR : 1≤ R)
    (hlogR : (1/4-ε/2)*log (N:ℝ)-log 2≤ log (R:ℝ)) :
    ((20/sqrt R)*exp (1096+log (N:ℝ)/16))*liuSingularSeries N≤1 := by
  have hRp : (0:ℝ)<R := by exact_mod_cast (show 0<R by omega)
  have hroot : 1/sqrt (R:ℝ)=exp (-log (R:ℝ)/2) := by
    rw [sqrt_eq_rpow,rpow_def_of_pos hRp,one_div,← exp_neg]
    congr 1
    ring
  have hlog2 : log (2:ℝ)≤1 := by linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have he : 1096+log (N:ℝ)/16+(822+3*log (N:ℝ)/64)-log (R:ℝ)/2≤-20 := by
    have hεL := mul_le_mul_of_nonneg_right hε (show 0 ≤ log (N:ℝ) by linarith only [hL])
    linarith only [hL,hlogR,hlog2,hεL]
  have h20 : (20:ℝ)≤ exp 20 := by linarith only [add_one_le_exp (20:ℝ)]
  calc
    _ ≤ ((20/sqrt R)*exp (1096+log (N:ℝ)/16))*exp (822+3*log (N:ℝ)/64) :=
      mul_le_mul_of_nonneg_left (expanded_singular_series_cap hN) (by positivity)
    _ = 20*exp (1096+log (N:ℝ)/16+(822+3*log (N:ℝ)/64)-log (R:ℝ)/2) := by
      rw [show (20:ℝ)/sqrt R=20*(1/sqrt R) by ring,hroot]
      calc
        _ = 20*(exp (-log (R:ℝ)/2)*exp (1096+log (N:ℝ)/16)*
            exp (822+3*log (N:ℝ)/64)) := by ring
        _ = _ := by rw [← exp_add,← exp_add]; congr 1; ring
    _ ≤ 20*exp (-20:ℝ) := mul_le_mul_of_nonneg_left (exp_le_exp.mpr he) (by norm_num)
    _ ≤ 1 := by
      have hh := mul_le_mul_of_nonneg_right h20 (exp_pos (-20:ℝ)).le
      rw [← exp_add] at hh
      norm_num at hh
      exact hh

theorem denominator_81_of_log {N : ℕ} {ε : ℝ} (hε : ε ≤ 1/1000)
    (hL : (130690:ℝ)≤ log (N:ℝ)) (hEven : Even N) :
    log (N:ℝ)/((81/10:ℝ)*liuSingularSeries N)≤ liuSelbergDenominator N ε := by
  have hn : 0<N := by
    by_contra h
    have hh : N=0 := by omega
    subst N
    norm_num at hL
  have hnR : (0:ℝ)<N := by exact_mod_cast hn
  have hN256 : 256≤ N := by
    have hh := log_le_sub_one_of_pos hnR
    exact_mod_cast (by linarith only [hh,hL] : (256:ℝ)≤ N)
  obtain ⟨hlogR,hR⟩ := numerical_selberg_log_floor hN256
    (show (1/8:ℝ)≤1/4-ε/2 by linarith only [hε])
  change 2≤ paperQSourceCutoff N ε at hR
  change (1/4-ε/2)*log (N:ℝ)-log 2≤ log (paperQSourceCutoff N ε:ℝ) at hlogR
  have hexp := selberg_uniform_two_term_expansion hEven hn (show 1≤ paperQSourceCutoff N ε by omega)
  rw [← liuSelbergDenominator_eq_sum_Icc hEven (by omega)] at hexp
  have hlo := (abs_le.mp hexp).1
  have hSp := liuSingularSeries_pos N
  have hmul := mul_le_mul_of_nonneg_right hlo hSp.le
  have herr := normalized_error hε hn hL (show 1≤ paperQSourceCutoff N ε by omega) hlogR
  have hc := (selberg_specialized_secondary_pos N).le
  have hmain : ((log (paperQSourceCutoff N ε:ℝ)+selbergSpecializedSecondary N)/
      (2*liuSingularSeries N))*liuSingularSeries N=
      (log (paperQSourceCutoff N ε:ℝ)+selbergSpecializedSecondary N)/2 := by field_simp
  rw [sub_mul,hmain] at hmul
  apply (div_le_iff₀ (mul_pos (by norm_num) hSp)).mpr
  have hl2 : log (2:ℝ)≤1 := by linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hεL := mul_le_mul_of_nonneg_right hε (show 0≤ log (N:ℝ) by linarith only [hL])
  nlinarith only [hmul,herr,hc,hlogR,hL,hl2,hεL]


theorem denominator_at_target {N : ℕ} (hN : targetCutoff ≤ N)
    (hEven : Even N) {ε : ℝ} (hε : ε ≤ 1/1000) :
    log (N:ℝ)/((81/10:ℝ)*liuSingularSeries N) ≤ liuSelbergDenominator N ε :=
  denominator_81_of_log hε (target_log_lower hN) hEven

#print axioms denominator_at_target
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenRadiusBudget -/
/-! Joint choice of the actual Selberg radius and its main coefficient.
The radius can now match the GRH distribution level N^0.498. No complete
triple estimate is asserted merely from this denominator bound. -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Finset
open MathlibNt.SieveTheory LiuWeight SingularSeries
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
theorem normalized_radius_error {N R : ℕ} {ε : ℝ} (hε : ε ≤ 9/2500)
    (hN : 0<N) (hL : (130690:ℝ)≤ log (N:ℝ)) (hR : 1≤ R)
    (hlogR : (1/4-ε/2)*log (N:ℝ)-log 2≤ log (R:ℝ)) :
    ((20/sqrt R)*exp (1096+log (N:ℝ)/16))*liuSingularSeries N≤1 := by
  have hRp : (0:ℝ)<R := by exact_mod_cast (show 0<R by omega)
  have hroot : 1/sqrt (R:ℝ)=exp (-log (R:ℝ)/2) := by
    rw [sqrt_eq_rpow,rpow_def_of_pos hRp,one_div,← exp_neg]
    congr 1
    ring
  have hlog2 : log (2:ℝ)≤1 := by linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have he : 1096+log (N:ℝ)/16+(822+3*log (N:ℝ)/64)-log (R:ℝ)/2≤-4 := by
    have hεL := mul_le_mul_of_nonneg_right hε (show 0 ≤ log (N:ℝ) by linarith only [hL])
    linarith only [hL,hlogR,hlog2,hεL]
  have h20 : (20:ℝ)≤ exp 4 := by
    have he := sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤4) 4
    norm_num [Finset.sum_range_succ] at he
    linarith only [he]
  calc
    _ ≤ ((20/sqrt R)*exp (1096+log (N:ℝ)/16))*exp (822+3*log (N:ℝ)/64) :=
      mul_le_mul_of_nonneg_left (expanded_singular_series_cap hN) (by positivity)
    _ = 20*exp (1096+log (N:ℝ)/16+(822+3*log (N:ℝ)/64)-log (R:ℝ)/2) := by
      rw [show (20:ℝ)/sqrt R=20*(1/sqrt R) by ring,hroot]
      calc
        _ = 20*(exp (-log (R:ℝ)/2)*exp (1096+log (N:ℝ)/16)*
            exp (822+3*log (N:ℝ)/64)) := by ring
        _ = _ := by rw [← exp_add,← exp_add]; congr 1; ring
    _ ≤ 20*exp (-4:ℝ) := mul_le_mul_of_nonneg_left (exp_le_exp.mpr he) (by norm_num)
    _ ≤ 1 := by
      have hh := mul_le_mul_of_nonneg_right h20 (exp_pos (-4:ℝ)).le
      rw [← exp_add] at hh
      norm_num at hh
      exact hh

theorem denominator_of_radius_budget {N : ℕ} {ε K : ℝ}
    (hε : ε ≤ 9/2500) (hK : 0 < K)
    (hgap : 1/K+(1/80000:ℝ) ≤ 1/8-ε/4)
    (hL : (130690:ℝ)≤ log (N:ℝ)) (hEven : Even N) :
    log (N:ℝ)/(K*liuSingularSeries N)≤ liuSelbergDenominator N ε := by
  have hn : 0<N := by
    by_contra h
    have hh : N=0 := by omega
    subst N
    norm_num at hL
  have hnR : (0:ℝ)<N := by exact_mod_cast hn
  have hN256 : 256≤ N := by
    have hh := log_le_sub_one_of_pos hnR
    exact_mod_cast (by linarith only [hh,hL] : (256:ℝ)≤ N)
  obtain ⟨hlogR,hR⟩ := numerical_selberg_log_floor hN256
    (show (1/8:ℝ)≤1/4-ε/2 by linarith only [hε])
  change 2≤ paperQSourceCutoff N ε at hR
  change (1/4-ε/2)*log (N:ℝ)-log 2≤ log (paperQSourceCutoff N ε:ℝ) at hlogR
  have hexp := selberg_uniform_two_term_expansion hEven hn (show 1≤ paperQSourceCutoff N ε by omega)
  rw [← liuSelbergDenominator_eq_sum_Icc hEven (by omega)] at hexp
  have hlo := (abs_le.mp hexp).1
  have hSp := liuSingularSeries_pos N
  have hmul := mul_le_mul_of_nonneg_right hlo hSp.le
  have herr := normalized_radius_error hε hn hL (show 1≤ paperQSourceCutoff N ε by omega) hlogR
  have hc := (selberg_specialized_secondary_pos N).le
  have hmain : ((log (paperQSourceCutoff N ε:ℝ)+selbergSpecializedSecondary N)/
      (2*liuSingularSeries N))*liuSingularSeries N=
      (log (paperQSourceCutoff N ε:ℝ)+selbergSpecializedSecondary N)/2 := by field_simp
  rw [sub_mul,hmain] at hmul
  have hl2 : log (2:ℝ) ≤ 1 := by
    linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hpaid := mul_le_mul_of_nonneg_right hgap
    (show 0 ≤ log (N:ℝ) by linarith only [hL])
  have hlinear : log (N:ℝ)/K ≤ liuSelbergDenominator N ε*liuSingularSeries N := by
    rw [div_eq_mul_inv]
    simp only [one_div] at hpaid
    nlinarith only [hmul,herr,hc,hlogR,hL,hl2,hpaid]
  rw [← div_div]
  exact (div_le_iff₀ hSp).mpr hlinear


theorem denominator_8049_at_target {N : ℕ} (hN : targetCutoff ≤ N)
    (hEven : Even N) :
    log (N:ℝ)/((8059/1000:ℝ)*liuSingularSeries N) ≤
      liuSelbergDenominator N (9/2500:ℝ) := by
  exact denominator_of_radius_budget (by norm_num) (by norm_num)
    (by norm_num) (target_log_lower hN) hEven

theorem improved_radius_margin :
    (2.00825:ℝ)-((8059/1000:ℝ)*(0.49254+1/10000)+1/1000)/2 =
      (0.02265712:ℝ) := by norm_num

#print axioms denominator_8049_at_target
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenTripleBridge -/
/-! The actual triple-to-square bridge at the proposed H<14 cutoff.
The square estimate is an explicit premise. No numerical estimate of the
square remainder is inferred from the denominator alone. -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Finset
open MathlibNt.SieveTheory LiuWeight SingularSeries SwitchingPrinciple
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem triple_residual_cutoff_le_target : tripleResidualThreshold ≤ targetCutoff := by
  rw [targetCutoff_eq]
  unfold tripleResidualThreshold logPowerCutoff
  exact Nat.pow_le_pow_right (by norm_num) (by norm_num)

theorem triple_of_square_at_target {N : ℕ} (hN : targetCutoff ≤ N)
    (hEven : Even N) {ε A E : ℝ} (hε : 0 ≤ ε) (hεHalf : ε ≤ 1/2)
    (hSquare : liuSelbergSquareCount N ε (liuSelbergOptimalLambda N ε) ≤
      A*(liuSingularSeries N*N/log (N:ℝ)^2)+E) :
    correctedChenTriplePenalty N ≤
      A*(liuSingularSeries N*N/log (N:ℝ)^2)+E+19*N/log (N:ℝ)^3 := by
  have hres := triple_residual_cutoff_le_target.trans hN
  have hlarge := tripleResidualThreshold_large.trans hres
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hR : 1 ≤ paperQSourceCutoff N ε := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using Real.one_le_rpow hN1
      (show 0 ≤ 1/4-ε/2 by linarith only [hεHalf])
  have hs := liuSelbergCorrectedSourceTripleCount_le_square_add_QResidual
    (epsilon:=ε) hEven hR
  have hc := explicit_triple_complement hres
  have hp := explicit_triple_paper_residual hres ε hε
  unfold correctedChenTriplePenalty
  calc
    _ ≤ liuSelbergCorrectedSourceTripleCount N+13*N/log (N:ℝ)^3 := hc
    _ ≤ (liuSelbergSquareCount N ε (liuSelbergOptimalLambda N ε)+
        liuSelbergCorrectedSourceTripleQResidual N ε)+13*N/log (N:ℝ)^3 :=
      add_le_add hs le_rfl
    _ ≤ (A*(liuSingularSeries N*N/log (N:ℝ)^2)+E+6*N/log (N:ℝ)^3)+
        13*N/log (N:ℝ)^3 := add_le_add (add_le_add hSquare hp) le_rfl
    _ = _ := by ring

theorem triple_residual_payment {N : ℕ} (hN : targetCutoff ≤ N) :
    19*N/log (N:ℝ)^3 ≤
      (1/3000:ℝ)*(liuSingularSeries N*N/log (N:ℝ)^2) := by
  have hL := target_log_lower hN
  have hl : 0 < log (N:ℝ) := by linarith only [hL]
  have hS := half_le_liuSingularSeries N
  have hcoeff : (19:ℝ)/log (N:ℝ) ≤ (1/3000:ℝ)*liuSingularSeries N := by
    apply (div_le_iff₀ hl).mpr
    have hh := mul_le_mul_of_nonneg_right hS hl.le
    nlinarith only [hh,hL]
  have hp := mul_le_mul_of_nonneg_right hcoeff
    (show 0 ≤ (N:ℝ)/log (N:ℝ)^2 by positivity)
  convert hp using 1 <;> field_simp [hl.ne']


end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenTripleUpper -/
/-! The actual square and corrected triple estimates at the target.
The distribution remainder is supplied by the explicit Pan assembly. -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Finset
open MathlibNt.SieveTheory LiuWeight SingularSeries SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem selberg_square_at_target {N : ℕ} (hN : targetCutoff≤ N) (hEven : Even N) :
    liuSelbergSquareCount N (9/2500:ℝ) (liuSelbergOptimalLambda N (9/2500:ℝ)) ≤
      ((8059/1000:ℝ)*0.498+1/1000)*
        (liuSingularSeries N*N/log (N:ℝ)^2) := by
  let ε : ℝ := 9/2500
  let lam := liuSelbergOptimalLambda N ε
  let K : ℝ := 8059/1000
  have hN9 := (logPowerCutoff_nine_le 0).trans (pan_log_cutoff_at_target (k:=0) (by norm_num) hN)
  have hn1 : (1:ℝ)≤ N := by exact_mod_cast (show 1≤ N by omega)
  have hR : 1≤ paperQSourceCutoff N ε := by
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
      (by simpa [K,ε] using denominator_8049_at_target hN hEven)
    simpa using hh
  have hmain := liuSelbergMainTerm_le_of_componentBounds 2 (K-8) (0.498:ℝ)
    N ε lam hEven hadm (by norm_num [K]) (liuSingularSeries_pos N).le
    (log_pos (by exact_mod_cast (show 1<N by omega))) hcoef (numerical_prime_pair_main hN)
  have hr := numerical_selberg_remainder hN lam hadm
  have hp := selberg_remainder_paid hN
  rw [liuSelbergSquareCount_eq_switchedCount,
    liuSelbergSwitchedCount_eq_logarithmicIntegralMainTerm_add_remainder 2]
  have hh := add_le_add hmain ((le_abs_self _).trans (hr.trans hp))
  convert hh using 1 <;> dsimp [K,ε,lam] <;> ring

theorem triple_upper {N : ℕ} (hN : targetCutoff≤ N) (hEven : Even N) :
    correctedChenTriplePenalty N ≤
      (4.015:ℝ)*(liuSingularSeries N*N/log (N:ℝ)^2) := by
  have hh := triple_of_square_at_target hN hEven
    (ε:=(9/2500:ℝ)) (A:=(8059/1000:ℝ)*0.498+1/1000) (E:=0)
    (by norm_num) (by norm_num) (by simpa using selberg_square_at_target hN hEven)
  have hp := triple_residual_payment hN
  have hm : 0≤ liuSingularSeries N*N/log (N:ℝ)^2 :=
    div_nonneg (mul_nonneg (liuSingularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
  nlinarith only [hh,hp,hm]

#print axioms selberg_square_at_target
#print axioms triple_upper
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenChenBridge -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple

/-- Actual prime plus at-most-two-prime-factor representation at the explicit
cutoff. The complete lower and upper counting estimates supply all premises. -/
theorem chen_of_weighted_lower {N : ℕ} (hN : targetCutoff≤ N) (hEven : Even N)
    (hLower : (2.00825:ℝ)*(SingularSeries.liuSingularSeries N*N/Real.log (N:ℝ)^2)≤
      jurkatRichertWeightedCount N) :
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q := by
  have hN9 := (logPowerCutoff_nine_le 0).trans (pan_log_cutoff_at_target (k:=0) (by norm_num) hN)
  have hM : 0<SingularSeries.liuSingularSeries N*N/Real.log (N:ℝ)^2 :=
    div_pos (mul_pos (SingularSeries.liuSingularSeries_pos N)
      (by exact_mod_cast (show 0<N by omega)))
      (pow_pos (Real.log_pos (by exact_mod_cast (show 1<N by omega))) 2)
  have htriple := triple_upper hN hEven
  have hb := corrected_counting_bridge_public_of_nine_le hN9
  rw [correctedChenKeyCount_eq_jurkatRichertWeightedCount_sub_triple] at hb
  have hcard : 0<(chenGoodRepresentations N).card := by
    exact_mod_cast (show (0:ℝ)<((chenGoodRepresentations N).card:ℝ) by
      nlinarith only [hb,hLower,htriple,hM])
  obtain ⟨p,hp⟩ := Finset.card_pos.mp hcard
  simp only [chenGoodRepresentations,Finset.mem_filter,Finset.mem_range] at hp
  exact ⟨p,N-p,hp.2.1,MathlibNt.ChensTheorem.semiprime_iff.mp
    ⟨hp.2.2.1,hp.2.2.2⟩,by omega⟩

#print axioms chen_of_weighted_lower

theorem target_of_double_exp_14 {N : ℕ}
    (hN : Real.exp (Real.exp (14:ℝ))≤ N) : targetCutoff≤ N := by
  exact_mod_cast targetCutoff_lt_double_exp_14.le.trans hN

end ChenEffective.GRHQuarterChen
end
