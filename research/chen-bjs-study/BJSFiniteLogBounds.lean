import BJSCanonicalMertensUpper

/-! Rational, kernel-checkable upper certificates for logarithms. -/
noncomputable section
namespace ChenEffective
open Real Finset
set_option maxHeartbeats 0

def bjsLogUpper (r : ℚ) (k : ℕ) : ℚ :=
  let z := (r / 2^k - 1) / (r / 2^k + 1)
  k * (6931471808 / 10000000000) +
    2 * ((∑ i ∈ range 8, z^(2*i+1)/(2*i+1)) + z^17/(1-z^2))

theorem bjsLogUpper_valid (r : ℚ) (k : ℕ) (hr : (2 : ℚ)^k ≤ r) :
    log (r : ℝ) ≤ (bjsLogUpper r k : ℝ) := by
  let y : ℝ := (r : ℝ)/2^k
  let z : ℝ := (y-1)/(y+1)
  have hy : 1 ≤ y := by
    dsimp [y]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [one_mul, Rat.cast_pow, Rat.cast_ofNat] using (show ((2 : ℚ)^k : ℝ) ≤ (r : ℝ) by exact_mod_cast hr)
  have hz0 : 0 ≤ z := div_nonneg (by linarith only [hy]) (by linarith only [hy])
  have hz1 : z < 1 := (div_lt_one (by linarith only [hy])).mpr (by linarith only [hy])
  have heq : (1+z)/(1-z)=y := by
    dsimp [z]
    field_simp
    ring
  have ht := log_div_le_sum_range_add hz0 hz1 8
  rw [heq] at ht
  have hl : log (r : ℝ) = k*log 2+log y := by
    rw [show (r : ℝ) = 2^k*y by dsimp [y]; field_simp]
    rw [log_mul (by positivity) (by linarith only [hy]),log_pow]
  have hk : (k : ℝ)*log 2 ≤ k*(6931471808/10000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left (by linarith only [log_two_lt_d9]) (Nat.cast_nonneg k)
  have hc : (bjsLogUpper r k : ℝ) =
      k*(6931471808/10000000000 : ℝ)+
        2*((∑ i ∈ range 8, z^(2*i+1)/(2*i+1))+z^17/(1-z^2)) := by
    dsimp [bjsLogUpper,z,y]
    push_cast
    rfl
  rw [hc,hl]
  linarith only [ht,hk]

end ChenEffective
