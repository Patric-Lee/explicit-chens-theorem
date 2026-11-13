import BJSHybridPrimePowers

noncomputable section
namespace ChenEffective.HybridProduct
open Real
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

private theorem lower_power_div_sqrt {x a : ℝ} (hx : (3:ℝ)^16 ≤ x)
    (k : ℕ) (hk : (k:ℝ) ≤ 16*(1/2-a)) :
    x^a ≤ sqrt x/(3:ℝ)^k := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have ha : 0 ≤ 1/2-a := by
    nlinarith only [hk,show (0:ℝ) ≤ k from Nat.cast_nonneg k]
  have hr : (3:ℝ)^k ≤ x^(1/2-a) := by
    calc
      _ = (3:ℝ)^(k:ℝ) := (rpow_natCast _ _).symm
      _ ≤ (3:ℝ)^(16*(1/2-a)) :=
        rpow_le_rpow_of_exponent_le (by norm_num) hk
      _ = ((3:ℝ)^16)^(1/2-a) := by
        rw [← rpow_natCast,← rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
        norm_num only [Nat.cast_ofNat]
      _ ≤ _ := rpow_le_rpow (by positivity) hx ha
  apply (le_div_iff₀ (by positivity : (0:ℝ) < 3^k)).mpr
  calc
    _ ≤ x^a*x^(1/2-a) := mul_le_mul_of_nonneg_left hr (rpow_nonneg hx0.le _)
    _ = sqrt x := by rw [← rpow_add hx0]; simp [sqrt_eq_rpow]

/-- Explicit elementary bound on the higher prime powers. The global
seventeen-bound is used only at smaller roots and is then bootstrapped
through the Costa--Pereira inequality already present in Mathlib. -/
theorem prime_power_gap_two {x : ℝ} (hx : (3:ℝ)^16 ≤ x) :
    Chebyshev.psi x-Chebyshev.theta x ≤ 2*sqrt x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hl4 : log (4:ℝ) ≤ 7/5 := by
    rw [show (4:ℝ)=2^2 by norm_num,log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [log_two_lt_d9]
  have hb (a : ℝ) : Chebyshev.psi (x^a) ≤ (7/5)*x^a+17*x^(a/2) := by
    have hy := rpow_nonneg hx0.le a
    have ht := Chebyshev.theta_le_log4_mul_x hy
    have hg := prime_power_gap_seventeen (x^a)
    have hl := mul_le_mul_of_nonneg_right hl4 hy
    rw [sqrt_eq_rpow,← rpow_mul hx0.le] at hg
    have he : a*(1/2:ℝ)=a/2 := by ring
    rw [he] at hg
    linarith only [ht,hg,hl]
  have h2 := hb (1/2)
  have h3 := hb (1/3)
  have h5 := hb (1/5)
  have h13 := lower_power_div_sqrt hx 2 (by norm_num : (2:ℝ) ≤ 16*(1/2-1/3))
  have h15 := lower_power_div_sqrt hx 4 (by norm_num : (4:ℝ) ≤ 16*(1/2-1/5))
  have h14 := lower_power_div_sqrt hx 4 (by norm_num : (4:ℝ) ≤ 16*(1/2-1/4))
  have h16 := lower_power_div_sqrt hx 5 (by norm_num : (5:ℝ) ≤ 16*(1/2-1/6))
  have h110 := lower_power_div_sqrt hx 6 (by norm_num : (6:ℝ) ≤ 16*(1/2-1/10))
  have hc := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  norm_num only [one_div] at hc
  norm_num only [div_div,one_mul,Nat.reducePow] at h2 h3 h5 h13 h15 h14 h16 h110
  rw [← sqrt_eq_rpow] at hc h2
  nlinarith only [hc,h2,h3,h5,h13,h15,h14,h16,h110,sqrt_nonneg x]

#print axioms prime_power_gap_two
end ChenEffective.HybridProduct
