import NumericalSmallQuotient

/-!
# A polynomial profile for the actual terminal tail

Unlike a constant terminal error, this estimate retains decay in the internal
recursive coordinate. It is uniform in the actual depth. It is intended for
an additional, unperturbed error term; multiplying the polynomial profile by
the original perturbation factor would destroy its tail-integral bound.
-/

open scoped Classical BigOperators
namespace ChenEffective
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1800000

theorem polynomial_coordinate_factorial_bound {x L : ℝ} (hx : 2 ≤ x) (hL : 0 ≤ L) :
    x ^ 4 * (L ^ (⌊x - 2⌋₊ + 1) / ((⌊x - 2⌋₊ + 1).factorial : ℝ) *
      Real.exp L) ≤ 256 * Real.exp (17 * L) := by
  let m := ⌊x - 2⌋₊ + 1
  have hxm : x ≤ (m : ℝ) + 2 := by
    have hh := Nat.lt_floor_add_one (x - 2)
    dsimp [m]
    push_cast
    linarith only [hh]
  have hm2 : m + 2 ≤ 2 ^ (m + 2) := (m + 2).lt_two_pow_self.le
  have hx2 : x ≤ (2 : ℝ) ^ (m + 2) := hxm.trans (by exact_mod_cast hm2)
  have hxpow : x ^ 4 ≤ 256 * (16 : ℝ) ^ m := by
    have hh := pow_le_pow_left₀ (by linarith only [hx] : 0 ≤ x) hx2 4
    apply hh.trans_eq
    rw [pow_add, mul_pow, ← pow_mul, Nat.mul_comm m 4, pow_mul]
    norm_num
    ring
  have hterm := Real.pow_div_factorial_le_exp (16 * L) (by positivity) m
  have hterm0 : 0 ≤ L ^ m / (m.factorial : ℝ) * Real.exp L := by positivity
  calc
    _ ≤ (256 * (16 : ℝ) ^ m) * (L ^ m / (m.factorial : ℝ) * Real.exp L) :=
      mul_le_mul_of_nonneg_right hxpow hterm0
    _ = 256 * ((16 * L) ^ m / (m.factorial : ℝ)) * Real.exp L := by
      rw [mul_pow]
      ring
    _ ≤ 256 * Real.exp (16 * L) * Real.exp L := by gcongr
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- The actual tail, with a polynomial weight in the recursive coordinate.
The budget is a fixed power of the logarithmic local-product budget. -/
theorem numerical_actualT_polynomial_log_bound (S : BoundingSieve) {K A x : ℝ}
    (hK : 0 < K) (hlocal : HasDimensionOneLocalProductBound S K)
    (n q p : ℕ) (hq : 2 ≤ q) (hp : p = ⌈(q : ℝ) ^ (1 / x)⌉₊)
    (hx : 2 ≤ x) (hA : Real.log (q : ℝ) ≤ A) :
    x ^ 4 * suzukiActualT S n q p ≤ 256 * (logarithmicR A K) ^ 17 := by
  have hp2 : 2 ≤ p := by
    rw [hp]
    have hh := Real.one_lt_rpow
      (show (1 : ℝ) < q by exact_mod_cast (show 1 < q by omega))
      (show 0 < 1 / x by positivity)
    have hc : 1 < ⌈(q : ℝ) ^ (1 / x)⌉₊ := Nat.lt_ceil.mpr (by simpa using hh)
    omega
  have hL : 0 ≤ suzukiSourceL (p : ℝ) K := by
    have hh := lemmaFourteenOne_localProduct_mass hlocal
      (show (2 : ℝ) ≤ p by exact_mod_cast hp2)
    have hm : 0 ≤ suzukiPrimeMassBelow S (p : ℝ) := by
      apply Finset.sum_nonneg
      intro t ht
      have htP := (Finset.mem_filter.mp ht).1
      exact (S.nu_pos_of_prime t (Nat.prime_of_mem_primeFactors htP)
        (Nat.mem_primeFactors.mp htP).2.1).le
    exact hm.trans hh
  have htail := suzukiLemma14_3_natCeil_uniform_explicit S (N := n) hlocal (by omega) hx hp
  have hscalar := polynomial_coordinate_factorial_bound hx hL
  have hqL : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hexp : Real.exp (suzukiSourceL (q : ℝ) K) =
      (Real.log (q : ℝ) / Real.log 2) * (1 + K / Real.log 2) := by
    unfold suzukiSourceL
    rw [Real.exp_add, Real.exp_log (by positivity), Real.exp_log (by positivity)]
  have hE : Real.exp (suzukiSourceL (p : ℝ) K) ≤ logarithmicR A K := by
    calc
      _ ≤ Real.exp (suzukiSourceL (q : ℝ) K) := Real.exp_le_exp.mpr
        (by rw [hp]; exact suzukiSourceL_natCeil_rpow_le hq hx)
      _ = _ := hexp
      _ ≤ _ := (numerical_logarithmic_bounds hq hK hA).1
  calc
    _ ≤ x ^ 4 * (suzukiSourceL (p : ℝ) K ^ (⌊x - 2⌋₊ + 1) /
        ((⌊x - 2⌋₊ + 1).factorial : ℝ) * Real.exp (suzukiSourceL (p : ℝ) K)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ ≤ 256 * Real.exp (17 * suzukiSourceL (p : ℝ) K) := hscalar
    _ = 256 * (Real.exp (suzukiSourceL (p : ℝ) K)) ^ 17 := by
      rw [show (17 : ℝ) = (17 : ℕ) by norm_num, Real.exp_nat_mul]
    _ ≤ _ := by gcongr

#print axioms numerical_actualT_polynomial_log_bound
end ChenEffective
