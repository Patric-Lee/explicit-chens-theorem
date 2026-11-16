import PlattNumericalAux
import PlattThetaInputs

noncomputable section
namespace ChenEffective.PlattWindow
open Real Set MeasureTheory AnalyticNumberTheory.Mertens
set_option maxHeartbeats 1800000

def endpointBudget : ℝ := (75/2)/(100000*23)

theorem log_lower_from {a x L : ℝ} (ha : 0 < a) (hax : a ≤ x)
    (hl : L ≤ log a) : L ≤ log x := hl.trans (log_le_log ha hax)

theorem log_dec_lower {x : ℝ} (n : ℕ) (hx : (10:ℝ)^n ≤ x) :
    (n:ℝ)*(23/10) ≤ log x :=
  log_lower_from (by positivity) hx (log_decimal n)

variable [Fact TernaryGoldbach.PlattZetaRH]

theorem thetaEndpoint_plateau {x : ℝ} (hx : (10:ℝ)^17 ≤ x) :
    |thetaEndpoint x| ≤ (1/2000000:ℝ)/39+1147/(300000000*39)+42*10^9/(10^17*39) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hl : (39:ℝ) ≤ log x := by
    have h := log_dec_lower 17 hx
    norm_num at h ⊢ <;> linarith only [h]
  have hl0 : 0 < log x := lt_of_lt_of_le (by norm_num) hl
  have hs : (300000000:ℝ) ≤ sqrt x :=
    le_sqrt_of_sq_le ((by norm_num : (300000000:ℝ)^2 ≤ 10^17).trans hx)
  have hs0 : 0 < sqrt x := sqrt_pos.mpr hx0
  have hθ := theta_plateau hx
  have he : ((1/2000000:ℝ)*x+1147*sqrt x+42*10^9)/(x*log x) =
      (1/2000000)/log x+1147/(sqrt x*log x)+42*10^9/(x*log x) := by
    field_simp [hx0.ne',hl0.ne',hs0.ne']
    nlinarith only [sq_sqrt hx0.le]
  unfold thetaEndpoint
  rw [abs_div,abs_of_pos (mul_pos hx0 hl0)]
  apply (div_le_div_of_nonneg_right hθ (by positivity)).trans
  rw [he]
  apply add_le_add
  · apply add_le_add
    · exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hl
    · exact div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (mul_le_mul hs hl (by norm_num) hs0.le)
  · exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul hx hl (by norm_num) hx0.le)

theorem thetaEndpoint_uniform {x : ℝ} (hx : (10:ℝ)^10 ≤ x) :
    |thetaEndpoint x| ≤ endpointBudget := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  by_cases h1 : x ≤ (3:ℝ)^22
  · have hl : (23:ℝ) ≤ log x := by
      have h := log_dec_lower 10 hx
      norm_num at h ⊢ <;> linarith only [h]
    exact thetaEndpoint_sqrt hx0 (by norm_num) (by norm_num) (by norm_num) hl
      ((by norm_num : (100000:ℝ)^2 ≤ 10^10).trans hx) (theta_first hx h1)
  have hx1 : (3:ℝ)^22 ≤ x := le_of_not_ge h1
  by_cases h2 : x ≤ (10:ℝ)^13
  · have hl : (24:ℝ) ≤ log x := by
      exact log_lower_from (by positivity) hx1 log_power_three_lower
    have h := thetaEndpoint_sqrt (C:=1177/25) (L:=24) (s:=(3:ℝ)^11) hx0
      (by norm_num) (by norm_num) (by positivity) hl
      ((by norm_num : ((3:ℝ)^11)^2 ≤ (3:ℝ)^22).trans hx1) (theta_second hx1 h2)
    exact h.trans (by norm_num [endpointBudget])
  have hx2 : (10:ℝ)^13 ≤ x := le_of_not_ge h2
  by_cases h3 : x ≤ (10:ℝ)^15
  · have hl : (29:ℝ) ≤ log x := by
      have h := log_dec_lower 13 hx2
      norm_num at h ⊢ <;> linarith only [h]
    have h := thetaEndpoint_sqrt (C:=74) (L:=29) (s:=3000000) hx0
      (by norm_num) (by norm_num) (by positivity) hl
      ((by norm_num : (3000000)^2 ≤ (10:ℝ)^13).trans hx2) (theta_third hx2 h3)
    exact h.trans (by norm_num [endpointBudget])
  have hx3 : (10:ℝ)^15 ≤ x := le_of_not_ge h3
  by_cases h4 : x ≤ (10:ℝ)^17
  · have hl : (34:ℝ) ≤ log x := by
      have h := log_dec_lower 15 hx3
      norm_num at h ⊢ <;> linarith only [h]
    have h := thetaEndpoint_sqrt (C:=202) (L:=34) (s:=30000000) hx0
      (by norm_num) (by norm_num) (by positivity) hl
      ((by norm_num : (30000000)^2 ≤ (10:ℝ)^15).trans hx3) (theta_fourth hx3 h4)
    exact h.trans (by norm_num [endpointBudget])
  have hx4 : (10:ℝ)^17 ≤ x := le_of_not_ge h4
  exact (thetaEndpoint_plateau hx4).trans (by norm_num [endpointBudget])

#print axioms thetaEndpoint_uniform
end ChenEffective.PlattWindow
