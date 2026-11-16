import PlattFiniteWindow
import PlattAnalyticWindow

noncomputable section
namespace ChenEffective.PlattWindow

/-- The fully assembled prefix window, conditional only on the explicitly
passed published modulus-one finite RH result. -/
theorem certified_prefix_window [Fact TernaryGoldbach.PlattZetaRH] :
    ∀ x : ℝ, 4000000≤x → x≤(3:ℝ)^120 →
      |reciprocalError x|≤(1/9000:ℝ) := by
  apply numerical_prefix_window_of_finite
  intro x hx hb
  simpa only [relativePrefix,finiteAllowance] using certified_finite_relative_window x hx hb

#print axioms certified_prefix_window
end ChenEffective.PlattWindow
