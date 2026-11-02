import ExplicitLogBounds
import NumericalThresholds
import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergCorrectedChenBridge

/-! Numerical endpoint and paper-modulus payments for Chen's triple bound.
The Selberg-square estimate is the sole remaining hypothesis in the final
triple estimate here. No new axioms. -/
namespace ChenEffective
open MathlibNt.SieveTheory
open SwitchingPrinciple LiuWeight SingularSeries
open Finset

def tripleResidualThreshold : ℕ := logPowerCutoff 36

theorem tripleResidualThreshold_large : 1024 ≤ tripleResidualThreshold := by
  calc
    1024 ≤ (3 : ℕ) ^ 7 := by norm_num
    _ ≤ 3 ^ (16 * (36 + 1) ^ 2) := Nat.pow_le_pow_right (by norm_num) (by norm_num)

theorem two_le_sourceZ10 {N : ℕ} (hN : 1024 ≤ N) : 2 ≤ liuSourceZ10 N := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hp : (2 : ℝ) ^ (10 : ℝ) ≤ N := by
    norm_num
    exact_mod_cast hN
  have hr := (Real.le_rpow_inv_iff_of_pos (by norm_num : (0 : ℝ) ≤ 2)
    hN0 (by norm_num : (0 : ℝ) < 10)).mpr hp
  unfold liuSourceZ10
  apply Nat.le_floor
  norm_num at hr ⊢
  exact hr

theorem explicit_triple_complement {N : ℕ} (hN : tripleResidualThreshold ≤ N) :
    (correctedChenCandidates N).sum (fun p =>
      tripleFactorCount (N - p) (correctedChenZ N) (correctedChenY N)) ≤
        liuSelbergCorrectedSourceTripleCount N + 13 * N / Real.log N ^ (3 : ℕ) := by
  have hlarge : 1024 ≤ N := tripleResidualThreshold_large.trans hN
  have hscale := power_saving_payment_explicit (k := 3) (m := 10)
    (by norm_num) (by norm_num : 10 * 3 ≤ 36) hN 13 (by norm_num)
  have hscale' : 13 * (N : ℝ) ^ (9 / 10 : ℝ) ≤ 13 * N / Real.log N ^ (3 : ℕ) := by
    convert hscale using 1
    norm_num
  exact (correctedChenTripleFactorSum_le_source_add_thirteen_mul_rpow_nine_tenths
    N (by omega) (two_le_sourceZ10 hlarge)).trans (add_le_add le_rfl hscale')

theorem explicit_triple_paper_residual {N : ℕ} (hN : tripleResidualThreshold ≤ N)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    liuSelbergCorrectedSourceTripleQResidual N epsilon ≤
      6 * N / Real.log N ^ (3 : ℕ) := by
  have hlarge : 1024 ≤ N := tripleResidualThreshold_large.trans hN
  have hscale := power_saving_payment_explicit (k := 3) (m := 12)
    (by norm_num) (by norm_num : 12 * 3 ≤ 36) hN 6 (by norm_num)
  have hscale' : 6 * (N : ℝ) ^ (11 / 12 : ℝ) ≤ 6 * N / Real.log N ^ (3 : ℕ) := by
    convert hscale using 1
    norm_num
  exact (liuSelbergCorrectedSourceTripleQResidual_le_six_mul_rpow_eleven_twelfths
    N epsilon (by omega) hepsilon).trans hscale'

/-- The only unspecified error coefficient in the triple estimate is the
one supplied by the Selberg-square bound: the other two add exactly 19. -/
theorem explicit_triple_from_square
    {N : ℕ} (hN : tripleResidualThreshold ≤ N) (hEven : Even N)
    (epsilon Csquare : ℝ) (hepsilon : 0 ≤ epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hSquare : liuSelbergSquareCount N epsilon (liuSelbergOptimalLambda N epsilon) ≤
      (3.94033 : ℝ) * liuSingularSeries N * N / Real.log N ^ (2 : ℕ) +
        Csquare * N / Real.log N ^ (3 : ℕ)) :
    correctedChenTriplePenalty N ≤
      (3.94033 : ℝ) * liuSingularSeries N * N / Real.log N ^ (2 : ℕ) +
        (Csquare + 19) * N / Real.log N ^ (3 : ℕ) := by
  have hlarge : 1024 ≤ N := tripleResidualThreshold_large.trans hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hR : 1 ≤ paperQSourceCutoff N epsilon := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using Real.one_le_rpow hN1
      (show 0 ≤ 1 / 4 - epsilon / 2 by linarith only [hepsilonHalf])
  have hsource := liuSelbergCorrectedSourceTripleCount_le_square_add_QResidual
    (epsilon := epsilon) hEven hR
  have hc := explicit_triple_complement hN
  have hp := explicit_triple_paper_residual hN epsilon hepsilon
  unfold correctedChenTriplePenalty
  calc
    _ ≤ liuSelbergCorrectedSourceTripleCount N + 13 * N / Real.log N ^ (3 : ℕ) := hc
    _ ≤ (liuSelbergSquareCount N epsilon (liuSelbergOptimalLambda N epsilon) +
          liuSelbergCorrectedSourceTripleQResidual N epsilon) +
            13 * N / Real.log N ^ (3 : ℕ) := add_le_add hsource le_rfl
    _ ≤ ((3.94033 : ℝ) * liuSingularSeries N * N / Real.log N ^ (2 : ℕ) +
          Csquare * N / Real.log N ^ (3 : ℕ) + 6 * N / Real.log N ^ (3 : ℕ)) +
            13 * N / Real.log N ^ (3 : ℕ) := add_le_add (add_le_add hSquare hp) le_rfl
    _ = _ := by ring

/-- Propagate an explicitly bounded square estimate through the recovered
finite counting endgame. Still requires a numerical square input and lower
estimate; neither is silently extracted from an eventual theorem. -/
theorem explicit_chen_from_square_estimates
    (nLower nSquare B : ℕ) (epsilon Csquare : ℝ)
    (hepsilon : 0 ≤ epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hB : Csquare + 19 ≤ B)
    (hLower : ∀ N : ℕ, nLower ≤ N → Even N →
      (2.6407 : ℝ) * liuSingularSeries N * N / Real.log N ^ (2 : ℕ) ≤
        jurkatRichertWeightedCount N)
    (hSquare : ∀ N : ℕ, nSquare ≤ N → Even N →
      liuSelbergSquareCount N epsilon (liuSelbergOptimalLambda N epsilon) ≤
        (3.94033 : ℝ) * liuSingularSeries N * N / Real.log N ^ (2 : ℕ) +
          Csquare * N / Real.log N ^ (3 : ℕ))
    {N : ℕ} (hN : chenCutoff nLower (max nSquare tripleResidualThreshold) B ≤ N)
    (hEven : Even N) :
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q = r * s) ∧ N = p + q := by
  apply explicit_chen_of_estimates nLower (max nSquare tripleResidualThreshold) B
    (Csquare + 19) hB hLower _ hN hEven
  intro M hM hMeven
  exact explicit_triple_from_square ((le_max_right _ _).trans hM) hMeven
    epsilon Csquare hepsilon hepsilonHalf (hSquare M ((le_max_left _ _).trans hM) hMeven)

#print axioms explicit_triple_from_square
#print axioms explicit_chen_from_square_estimates
end ChenEffective
