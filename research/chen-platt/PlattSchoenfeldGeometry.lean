import PlattThetaInputs
import PlattLogBounds

/-! Elementary geometry and psi-to-theta conversion for the proposed
finite-RH Schoenfeld branch. No analytic prime bound is assumed globally:
the source psi estimate is an explicit premise of the conversion theorem. -/
noncomputable section
namespace ChenEffective.PlattWindow.Schoenfeld
open Real
set_option autoImplicit false
set_option maxHeartbeats 1600000

def reference : ℝ := 2000000000
def analyticSplit : ℝ := (10:ℝ)^16

theorem reference_log : (21:ℝ) ≤ log reference := by
  have h := log_ten_lower
  have h2 := log_two_gt_d9
  have he : reference=2*(10:ℝ)^9 := by norm_num [reference]
  rw [he,log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity),log_pow]
  norm_num at h ⊢
  linarith only [h,h2]

theorem log_lower {x : ℝ} (hx : reference ≤ x) : (21:ℝ) ≤ log x :=
  reference_log.trans (log_le_log (by norm_num [reference]) hx)

/-- The finite-RH range condition is paid by the existing height10^8.
No extra zero computation is an input to this elementary lemma. -/
theorem height_condition {x : ℝ} (hx : reference ≤ x) (hxhi : x ≤ analyticSplit) :
    (4.92:ℝ)*sqrt (x/log x) ≤ 100000000 := by
  have hl := log_lower hx
  have hl0 : 0 < log x := lt_of_lt_of_le (by norm_num : (0:ℝ) < 21) hl
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num [reference]) hx
  have hratio : x/log x ≤ (100000000/(4.92:ℝ))^2 := by
    rw [div_le_iff₀ hl0]
    by_cases hsmall : x ≤ (10:ℝ)^15
    · nlinarith only [hsmall,hl]
    · have h15 := log_power_ten_lower 15
      have hmono := log_le_log (by positivity : (0:ℝ) < 10^15) (le_of_not_ge hsmall)
      norm_num at h15 hmono
      change x ≤ (100000000/(4.92:ℝ))^2*log x
      unfold analyticSplit at hxhi
      nlinarith only [h15,hmono,hxhi]
  have hs : sqrt (x/log x) ≤ 100000000/(4.92:ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num,hratio⟩
  nlinarith only [hs]

theorem prime_power_absorption {x : ℝ} (hx : reference ≤ x) :
    2*sqrt x ≤ (3/(8*Real.pi))*sqrt x*log x := by
  have hl := log_lower hx
  have hp := pi_lt_d2
  have hcoeff : (2:ℝ) ≤ 3/(8*Real.pi)*log x := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : (0:ℝ) < 8*Real.pi)).mpr
    nlinarith only [hl,hp]
  have hs : 0 ≤ sqrt x := sqrt_nonneg x
  calc
    _ ≤ (3/(8*Real.pi)*log x)*sqrt x := mul_le_mul_of_nonneg_right hcoeff hs
    _ = _ := by ring

/-- Transfer the normalized-psi bound, including its possible half-jump,
to the actual Mathlib theta function. This does not prove the source bound. -/
theorem theta_of_buthe_psi {x : ℝ} (hx : reference ≤ x)
    (hpsi : |Chebyshev.psi x-x| ≤
      sqrt x*log x*(log x-3)/(8*Real.pi)+log x/2) :
    |Chebyshev.theta x-x| ≤ sqrt x*(log x)^2/(8*Real.pi)+log x/2 := by
  have hxlarge : (3:ℝ)^16 ≤ x := (by norm_num [reference] : (3:ℝ)^16 ≤ reference).trans hx
  have h := theta_error_of_psi hxlarge hpsi
  have hm := prime_power_absorption hx
  have he : sqrt x*log x*(log x-3)/(8*Real.pi)+log x/2+
      (3/(8*Real.pi))*sqrt x*log x = sqrt x*(log x)^2/(8*Real.pi)+log x/2 := by ring
  exact h.trans (by rw [← he]; linarith only [hm])

#print axioms height_condition
#print axioms theta_of_buthe_psi
end ChenEffective.PlattWindow.Schoenfeld
