import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-! Exact arithmetic contracts for a research budget study.
These theorems do not prove analytic estimates, connect to the actual Chen
counts, or assert Chen's theorem at any new cutoff. The analytic estimates
are explicit hypotheses. No added axiom or numerical oracle is used. -/
noncomputable section
namespace ChenEffective.FiniteScaleStudy

def completeTripleCost (L : ℝ) : ℝ :=
  (403/50:ℝ)*(99/200)+60000000/L^3+38/L

theorem tripleCost_antitone {L₀ L : ℝ} (h₀ : 0<L₀) (h : L₀≤L) :
    completeTripleCost L ≤ completeTripleCost L₀ := by
  have hp : L₀^3≤L^3 := by gcongr
  have h₁ := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤60000000)
    (pow_pos h₀ 3) hp
  have h₂ := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤38) h₀ h
  unfold completeTripleCost
  linarith only [h₁,h₂]

theorem cost_H11 {L : ℝ} (h : 59874≤L) : completeTripleCost L≤3991/1000 :=
  (tripleCost_antitone (by norm_num) h).trans (by norm_num [completeTripleCost])

theorem cost_H10 {L : ℝ} (h : 22026≤L) : completeTripleCost L≤3992/1000 :=
  (tripleCost_antitone (by norm_num) h).trans (by norm_num [completeTripleCost])

theorem cost_H9 {L : ℝ} (h : 8103≤L) : completeTripleCost L≤3995/1000 :=
  (tripleCost_antitone (by norm_num) h).trans (by norm_num [completeTripleCost])

theorem cost_H8 {L : ℝ} (h : 2980≤L) : completeTripleCost L≤4005/1000 :=
  (tripleCost_antitone (by norm_num) h).trans (by norm_num [completeTripleCost])

theorem lower_coefficient :
    (3301/1250:ℝ)-17/250-(28/25)/2-1/20000=8051/4000 := by norm_num

/-- Pure algebra: the displayed numerical component estimates would suffice.
No hypothesis here is discharged for the actual representation counts. -/
theorem positive_of_actual_count_bounds {M W T R t : ℝ} (hM : 0<M)
    (hW : ((3301/1250:ℝ)-17/250-(28/25)/2-1/20000)*M≤W)
    (hT : T≤t*M) (hR : W-T/2≤R) (ht : t<8051/2000) :
    (8051/4000-t/2)*M≤R ∧ 0<R := by
  rw [lower_coefficient] at hW
  have hpaid : (8051/4000-t/2)*M≤R := by nlinarith only [hW,hT,hR]
  have hpos : 0<(8051/4000-t/2)*M := mul_pos (by linarith only [ht]) hM
  exact ⟨hpaid,hpos.trans_le hpaid⟩

theorem exact_margins :
    (8051/4000:ℝ)-(3991/1000)/2=69/4000 ∧
    (8051/4000:ℝ)-(3992/1000)/2=67/4000 ∧
    (8051/4000:ℝ)-(3995/1000)/2=61/4000 ∧
    (8051/4000:ℝ)-(4005/1000)/2=41/4000 := by norm_num

#print axioms cost_H11
#print axioms cost_H10
#print axioms cost_H9
#print axioms cost_H8
#print axioms positive_of_actual_count_bounds
#print axioms exact_margins
end ChenEffective.FiniteScaleStudy
end
