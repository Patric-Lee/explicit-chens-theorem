import PlattAssemblySoundness
import PlattAssemblyPilot.C000000Sound
import PlattAssemblyPilot.SealedTotals0N8
import PlattAssemblyPilot.SealedTotals9992N16
import PlattAssemblyPilot.Grid0N256

noncomputable section
namespace ChenEffective.PlattWindow.AssemblyPilot
open AnalyticNumberTheory.Mertens
set_option maxHeartbeats 3000000

theorem first_eight_chunks_bound :
    (4035733554828:ℝ) ≤ (2:ℝ)^48*(primeReciprocalSum 4980736-primeReciprocalSum 4000000) ∧
    (2:ℝ)^48*(primeReciprocalSum 4980736-primeReciprocalSum 4000000) ≤ (4035784694748:ℝ) := by
  exact checked_increment_summary_sound SealedTotals0N8.all_certified SealedTotals0N8.summary_checked

theorem counting_section_seam_bound :
    (21363104411:ℝ) ≤ (2:ℝ)^48*(primeReciprocalSum 1315700736-primeReciprocalSum 1313603584) ∧
    (2:ℝ)^48*(primeReciprocalSum 1315700736-primeReciprocalSum 1313603584) ≤ (21363123070:ℝ) := by
  exact checked_increment_summary_sound SealedTotals9992N16.all_certified SealedTotals9992N16.summary_checked

theorem first_grid_batch_covers {x : ℝ}
    (ha : (4000000:ℝ) ≤ x) (hb : x ≤ (4032768:ℝ)) :
    x=(4032768:ℝ) ∨ ∃ c ∈ Grid0N256.cells, (c.a:ℝ) ≤ x ∧ x ≤ (c.b:ℝ) := by
  exact checked_cell_chain_cover Grid0N256.seams_checked ha hb

#print axioms first_eight_chunks_bound
#print axioms first_grid_batch_covers
#print axioms counting_section_seam_bound
end ChenEffective.PlattWindow.AssemblyPilot
