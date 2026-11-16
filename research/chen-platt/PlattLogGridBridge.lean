import PlattLogRowSoundness
import PlattRelativeGrid

/-! Connect the kernel-checked fixed-point logarithm rows to real grid cells.
No prime counts or numerical prefix bounds are assumed to have been certified.
The prime-sum inequalities and the final scalar budget remain explicit inputs. -/
noncomputable section
set_option autoImplicit false
namespace ChenEffective.PlattWindow
open Real AnalyticNumberTheory.Mertens LogCertificate

theorem certified_loglog_bounds (r : LogRow) (h : checkRow r = true) :
    (r.lower : ℝ) / scale ≤ log (log (r.x : ℝ)) ∧
      log (log (r.x : ℝ)) ≤ (r.upper : ℝ) / scale := by
  have hs : (0 : ℝ) < scale := by norm_num [scale]
  obtain ⟨hl, hu⟩ := checkRow_sound r h
  constructor
  · apply (div_le_iff₀ hs).2
    nlinarith only [hl]
  · apply (le_div_iff₀ hs).2
    nlinarith only [hu]

theorem certified_rows_loglog_bounds (rows : List LogRow)
    (h : rows.all checkRow = true) (r : LogRow) (hr : r ∈ rows) :
    (r.lower : ℝ) / scale ≤ log (log (r.x : ℝ)) ∧
      log (log (r.x : ℝ)) ≤ (r.upper : ℝ) / scale := by
  exact certified_loglog_bounds r ((List.all_eq_true.mp h) r hr)

/-- Once endpoint prime sums are available, existing log rows pay the real-cell
interpolation budget, including noninteger points and prime endpoints. -/
theorem certified_relative_cell_paid (a b r : LogRow) {x lower upper : ℝ}
    (ha : checkRow a = true) (hb : checkRow b = true) (hr : checkRow r = true)
    (ha1 : 1 < (a.x : ℝ)) (hax : (a.x : ℝ) ≤ x) (hxb : x ≤ (b.x : ℝ))
    (hlower : lower ≤ primeReciprocalSum a.x - primeReciprocalSum r.x)
    (hupper : primeReciprocalSum b.x - primeReciprocalSum r.x ≤ upper)
    (hlo : -finiteAllowance ≤ lower - (b.upper : ℝ) / scale + (r.lower : ℝ) / scale)
    (hhi : upper - (a.lower : ℝ) / scale + (r.upper : ℝ) / scale ≤ finiteAllowance) :
    |relativePrefix x (r.x : ℝ)| ≤ finiteAllowance := by
  obtain ⟨hal, _⟩ := certified_loglog_bounds a ha
  obtain ⟨_, hbu⟩ := certified_loglog_bounds b hb
  obtain ⟨hrl, hru⟩ := certified_loglog_bounds r hr
  apply relative_cell_paid ha1 hax hxb
    (by simpa only [Nat.floor_natCast] using hlower)
    (by simpa only [Nat.floor_natCast] using hupper) hal hbu hrl hru hlo hhi

#print axioms certified_rows_loglog_bounds
#print axioms certified_relative_cell_paid
end ChenEffective.PlattWindow
