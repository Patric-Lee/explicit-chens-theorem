import PlattGlobalBoundSoundness
import PlattGlobalTotals.L2B0000

noncomputable section
namespace ChenEffective.PlattWindow
open AnalyticNumberTheory.Mertens

/-- Entire finite reference increment, assembled from all completed count
chunks via the checked totals leaves and the bounded global sum tree. -/
theorem global_reference_reciprocal_bounds :
    (116863011702975:ℝ) ≤ (2:ℝ)^48*
      (primeReciprocalSum 10000000000-primeReciprocalSum 4000000) ∧
    (2:ℝ)^48*(primeReciprocalSum 10000000000-primeReciprocalSum 4000000) ≤
      (116863401833309:ℝ) :=
  reciprocalBound_sound GlobalTotals.L2B0000.bound

#print axioms global_reference_reciprocal_bounds
end ChenEffective.PlattWindow
