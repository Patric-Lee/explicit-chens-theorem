import GRH14ScalarBudget
import GRH14RadiusBudget
import ExplicitChenTriple

/-! The actual triple-to-square bridge at the proposed H<14 cutoff.
The square estimate is an explicit premise. No numerical estimate of the
square remainder is inferred from the denominator alone. -/
noncomputable section
namespace ChenEffective.GRH14
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
      (1/20000:ℝ)*(liuSingularSeries N*N/log (N:ℝ)^2) := by
  have hL := target_log_lower hN
  have hl : 0 < log (N:ℝ) := by linarith only [hL]
  have hS := half_le_liuSingularSeries N
  have hcoeff : (19:ℝ)/log (N:ℝ) ≤ (1/20000:ℝ)*liuSingularSeries N := by
    apply (div_le_iff₀ hl).mpr
    have hh := mul_le_mul_of_nonneg_right hS hl.le
    nlinarith only [hh,hL]
  have hp := mul_le_mul_of_nonneg_right hcoeff
    (show 0 ≤ (N:ℝ)/log (N:ℝ)^2 by positivity)
  convert hp using 1 <;> field_simp [hl.ne']

/-- A square estimate with this explicit remaining error budget suffices
for the proposed Chen endgame. -/
theorem chen_of_lower_and_square {N : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N)
    (hLower : (2.02575:ℝ)*(liuSingularSeries N*N/log (N:ℝ)^2) ≤
      jurkatRichertWeightedCount N)
    (hSquare : liuSelbergSquareCount N (1/500:ℝ)
        (liuSelbergOptimalLambda N (1/500:ℝ)) ≤
      ((81/10:ℝ)*(0.49254+1/10000)+19/20000)*
        (liuSingularSeries N*N/log (N:ℝ)^2)) :
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q := by
  apply representation_of_target_counts hN hLower
  have ht := triple_of_square_at_target hN hEven
    (ε:=(1/500:ℝ)) (A:=((81/10:ℝ)*(0.49254+1/10000)+19/20000))
    (E:=0) (by norm_num) (by norm_num) (by simpa using hSquare)
  have hp := triple_residual_payment hN
  nlinarith only [ht,hp]

#print axioms chen_of_lower_and_square
end ChenEffective.GRH14
