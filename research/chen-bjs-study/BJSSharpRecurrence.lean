import BJSSharpHat

/-! Rational caps for the refined error recursion at the ACTUAL relative
product error 1/4000. The target density error 110/2000 therefore permits
a parity sum of 220. These scalar caps do not assert the missing layer table.
-/
namespace ChenEffective
set_option maxHeartbeats 2000000

theorem bjsStudy_even_error_coefficient {ε : ℝ} (hε : 0 ≤ ε) (hc : ε ≤ 1/4000) :
    (1+ε)^2*(241/250 : ℝ)+(1+ε)*ε*(11/3) ≤ 1931/2000 := by
  nlinarith [mul_nonneg hε (sub_nonneg.mpr hc)]

theorem bjsStudy_odd_error_coefficient {ε : ℝ} (hε : 0 ≤ ε) (hc : ε ≤ 1/4000) :
    (1+ε)^2*(116/125 : ℝ)+(1+ε)*ε*(11/3) ≤ 1859/2000 := by
  nlinarith [mul_nonneg hε (sub_nonneg.mpr hc)]

theorem bjsStudy_profile_forcing_cap {ε a b : ℝ}
    (hc : ε ≤ 1/4000) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (22/3 : ℝ)*(1+ε)*a+2*(2+ε)*b ≤ (367/50 : ℝ)*a+(401/100 : ℝ)*b := by
  have h1 : (22/3 : ℝ)*(1+ε) ≤ 367/50 := by linarith only [hc]
  have h2 : 2*(2+ε) ≤ (401/100 : ℝ) := by linarith only [hc]
  exact add_le_add (mul_le_mul_of_nonneg_right h1 ha) (mul_le_mul_of_nonneg_right h2 hb)

theorem bjsStudy_density_error_payment :
    (1/4000 : ℝ)*220=110*(1/2000 : ℝ) := by norm_num

#print axioms bjsStudy_even_error_coefficient
#print axioms bjsStudy_odd_error_coefficient
#print axioms bjsStudy_profile_forcing_cap
end ChenEffective
