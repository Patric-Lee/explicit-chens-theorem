import BJSSelbergSpecialization
import ChenBudget

/-! Joint coefficient accounting. All analytic inputs in the existence
adapter are actual bounds on the project's counts, not paper coefficients.
The examples certify allocations only, not a new small-cutoff theorem. -/
noncomputable section
namespace ChenEffective
open Real
open MathlibNt.SieveTheory LiuWeight SingularSeries SwitchingPrinciple

def jointSelbergBudget (K η extra remainder : ℝ) : ChenBudget :=
  ⟨1/20,113/100,1/20000,K*(0.49254+η)+extra,remainder⟩

theorem joint_selberg_margin (K η extra remainder : ℝ) :
    (jointSelbergBudget K η extra remainder).margin =
      2.02575-(K*(0.49254+η)+extra+remainder)/2 := by
  unfold jointSelbergBudget ChenBudget.margin ChenBudget.weighted
  ring

/-- This is the exact budget available for a weaker denominator coefficient. -/
theorem joint_selberg_margin_pos_iff (K η extra remainder : ℝ) :
    0 < (jointSelbergBudget K η extra remainder).margin ↔
      K*(0.49254+η)+extra+remainder < 4.0515 := by
  rw [joint_selberg_margin]
  constructor <;> intro h <;> linarith

theorem joint_selberg_81_margin :
    (jointSelbergBudget (81/10) (1/10^7) (1/10^5) (1/100)).margin =
      (0.025957595 : ℝ) := by
  rw [joint_selberg_margin]
  norm_num

theorem joint_selberg_82_margin :
    (jointSelbergBudget (82/10) (1/10^7) (1/10^5) (1/100)).margin =
      (0.00133059 : ℝ) := by
  rw [joint_selberg_margin]
  norm_num

theorem joint_selberg_existence {N : ℕ} (hN : 9 ≤ N)
    {K η extra remainder : ℝ}
    (hmargin : K*(0.49254+η)+extra+remainder < 4.0515)
    (hlower : (2.02575 : ℝ)*(liuSingularSeries N*N/log (N : ℝ)^2) ≤
      jurkatRichertWeightedCount N)
    (htriple : correctedChenTriplePenalty N ≤
      (K*(0.49254+η)+extra+remainder)*(liuSingularSeries N*N/log (N : ℝ)^2)) :
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q := by
  apply chen_budget_existence (jointSelbergBudget K η extra remainder) hN
    ((joint_selberg_margin_pos_iff K η extra remainder).mpr hmargin)
  · convert hlower using 1
    norm_num [jointSelbergBudget,ChenBudget.weighted]
  · simpa only [jointSelbergBudget] using htriple

#print axioms joint_selberg_existence
end ChenEffective
