import GRH14TripleUpper
import Goldbach.Statement

noncomputable section
namespace ChenEffective.GRH14
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple

/-- Actual prime plus at-most-two-prime-factor representation at the explicit
cutoff. The complete lower and upper counting estimates supply all premises. -/
theorem chen_of_weighted_lower {N : ℕ} (hN : targetCutoff≤N) (hEven : Even N)
    (hLower : (2.02575:ℝ)*(SingularSeries.liuSingularSeries N*N/Real.log (N:ℝ)^2)≤
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
    (hN : Real.exp (Real.exp (14:ℝ))≤N) : targetCutoff≤N := by
  exact_mod_cast targetCutoff_lt_double_exp_14.le.trans hN

end ChenEffective.GRH14


