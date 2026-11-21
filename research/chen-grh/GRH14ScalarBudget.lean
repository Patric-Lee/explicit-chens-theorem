import GRH14ErrorBudget
import MathlibNt.SieveTheory.Switching.WeightedCounting
import MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries
import MathlibNt.ChensTheorem

/-! Conditional adapter for actual Chen counts at the H<14 target. The
analytic lower and complete triple inequalities remain explicit premises. -/
noncomputable section
open Real
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
namespace ChenEffective.GRH14
/-- These are bounds on actual counts, not numerical sieve axioms. -/
theorem representation_of_target_counts {N : ℕ} (hN : targetCutoff ≤ N)
    (hlower : (2.02575 : ℝ)*(SingularSeries.liuSingularSeries N*N/log (N : ℝ)^2) ≤
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
end ChenEffective.GRH14
