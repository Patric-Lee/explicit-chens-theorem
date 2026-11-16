import PlattLogRows
import PlattLogSoundness
noncomputable section
namespace ChenEffective.PlattWindow.LogCertificate
theorem checkRow_sound (r : LogRow) (h : checkRow r = true) :
    (r.lower:ℝ) ≤ (scale:ℝ)*Real.log (Real.log (r.x:ℝ)) ∧
    (scale:ℝ)*Real.log (Real.log (r.x:ℝ)) ≤ (r.upper:ℝ) := by
  simp only [checkRow,decide_eq_true_eq] at h
  rcases h with ⟨hx,hxl,hxu,hfirst,hL,hll,hlu,hul,huu,hlcert,hucert⟩
  exact loglog_of_certificates hx hxl hxu hfirst hL hll hlu hul huu hlcert hucert

theorem checkedRows_sound (rows : List LogRow) (h : rows.all checkRow = true)
    (r : LogRow) (hr : r ∈ rows) :
    (r.lower:ℝ) ≤ (scale:ℝ)*Real.log (Real.log (r.x:ℝ)) ∧
    (scale:ℝ)*Real.log (Real.log (r.x:ℝ)) ≤ (r.upper:ℝ) := by
  exact checkRow_sound r ((List.all_eq_true.mp h) r hr)
#print axioms checkedRows_sound
end ChenEffective.PlattWindow.LogCertificate
