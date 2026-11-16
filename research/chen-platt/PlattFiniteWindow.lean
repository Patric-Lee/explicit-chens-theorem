import PlattGlobalPointCover
import PlattFiniteWindowSoundness

noncomputable section
namespace ChenEffective.PlattWindow
open Real AnalyticNumberTheory.Mertens
set_option maxHeartbeats 3000000

/-- The entire finite relative window, from independently checked sieve,
fixed-point reciprocal sums, logarithm certificates, and covering grid cells. -/
theorem certified_finite_relative_window (x : ℝ)
    (hx : 4000000≤x) (hxb : x≤(10:ℝ)^10) :
    |relativePrefix x ((10:ℝ)^10)|≤1/20000 :=
  finite_relative_window_of_certificates PointPackets.L2B0000.certified
    GlobalGrid.L1B0000.certified global_grid_points_covered x hx hxb

#print axioms certified_finite_relative_window
end ChenEffective.PlattWindow
