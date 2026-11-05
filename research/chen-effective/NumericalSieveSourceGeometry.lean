import NumericalSieveSourceStep
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144IHInstantiation

namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers KappaOneModel
open SuzukiLemma144Equation1410
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem natural_root_le_of_power_le {D p m : ℕ} (hp : 0 < p) (hm : 0 < m)
    (h : D ≤ p ^ m) : (D : ℝ) ^ (1 / (m : ℝ)) ≤ p := by
  have hr := Real.rpow_inv_le_iff_of_pos (x := (D : ℝ)) (y := (p : ℝ)) (z := (m : ℝ))
    (by positivity) (by positivity) (by exact_mod_cast hm)
  rw [← one_div, rpow_natCast] at hr
  exact hr.mpr (by exact_mod_cast h)

theorem natural_power_lt_of_lt_root {D p m : ℕ} (hD : 0 < D) (hm : 0 < m)
    (h : (p : ℝ) < (D : ℝ) ^ (1 / (m : ℝ))) : p ^ m < D := by
  have hr := Real.lt_rpow_inv_iff_of_pos (x := (p : ℝ)) (y := (D : ℝ)) (z := (m : ℝ))
    (by positivity) (by positivity) (by exact_mod_cast hm)
  rw [← one_div, rpow_natCast] at hr
  exact_mod_cast hr.mp h

theorem actual_source_carrier_geometry {S : BoundingSieve} {n D p : ℕ} {s : ℝ}
    (hn : 0 < n) (hD : 1 < D) (hs : s ∈ closedDomain 2 (n + 1))
    (hp : p ∈ suzukiSourceOuterCarrierPowerReal (n + 1) D
      ((D : ℝ) ^ (1 / s)) S.prodPrimes.primeFactors) :
    (D : ℝ) ^ (1 / ((n : ℝ) + 3)) ≤ (p : ℝ) ∧
      (p : ℝ) < (D : ℝ) ^ (1 / max s (2 + (eps (n + 1) : ℝ))) := by
  have hpP := (mem_filter.mp (mem_filter.mp hp).1).1
  have hpPrime := Nat.prime_of_mem_primeFactors hpP
  have hpx := (mem_filter.mp (mem_filter.mp hp).1).2
  have hpLower := (mem_filter.mp hp).2.1
  have hpOdd := (mem_filter.mp hp).2.2
  constructor
  · have hh := natural_root_le_of_power_le hpPrime.pos (show 0 < n + 1 + 2 by omega) hpLower
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, show (1 : ℝ) + 2 = 3 by norm_num] using hh
  · by_cases he : eps (n + 1) = 0
    · have hs2 : 2 ≤ s := by simpa only [closedDomain, Set.mem_Ici, he, Nat.cast_zero, sub_zero] using hs
      simpa only [he, Nat.cast_zero, add_zero, max_eq_left hs2] using hpx
    · have he1 : eps (n + 1) = 1 := by unfold eps at *; omega
      by_cases hs3 : 3 ≤ s
      · simpa only [he1, Nat.cast_one, show (2 : ℝ) + 1 = 3 by norm_num, max_eq_left hs3] using hpx
      · have hodd : Odd (n + 1) := Nat.odd_iff.mpr he1
        have hcube : p ^ 3 < D := hpOdd hodd
        have hr := Real.lt_rpow_inv_iff_of_pos (x := (p : ℝ)) (y := (D : ℝ)) (z := (3 : ℝ))
          (by positivity) (by positivity) (by norm_num)
        have hroot : (p : ℝ) < (D : ℝ) ^ (1 / 3 : ℝ) := by
          rw [one_div]
          apply hr.mpr
          norm_num only [rpow_ofNat]
          exact_mod_cast hcube
        simpa only [he1, Nat.cast_one, show (2 : ℝ) + 1 = 3 by norm_num,
          max_eq_right (le_of_not_ge hs3)] using hroot

theorem sourceEuler_eq_real_product (S : BoundingSieve) (p : ℕ) :
    sourceDiscreteEuler S p = suzukiVProduct S (p : ℝ) := by
  unfold sourceDiscreteEuler suzukiVProduct suzukiSupportedBelow
  congr 1
  ext q
  simp

theorem actual_source_inner_transport {S : BoundingSieve} {n D p : ℕ} {s ε : ℝ}
    (hn : 0 < n) (hD : 1 < D) (hε : 0 ≤ ε) (hs : s ∈ closedDomain 2 (n + 1))
    (hp : p ∈ suzukiSourceOuterCarrierPowerReal (n + 1) D
      ((D : ℝ) ^ (1 / s)) S.prodPrimes.primeFactors)
    (hIH : ∀ D' z' : ℕ, ∀ s' : ℝ, 1 < D' → s' ∈ closedDomain 2 n →
      z' = ⌈(D' : ℝ) ^ (1 / s')⌉₊ →
      suzukiSourceV S n D' z' ≤ suzukiVProduct S ((D' : ℝ) ^ (1 / s')) *
        sourceLayerEnvelope n ε s') :
    suzukiSourceV S n (D ⌈/⌉ p) p ≤ sourceDiscreteEuler S p *
      sourceLayerTest n ε (log (D : ℝ) / log p) := by
  have hpP := (mem_filter.mp (mem_filter.mp hp).1).1
  have hpPrime := Nat.prime_of_mem_primeFactors hpP
  have hp2 : 2 ≤ p := hpPrime.two_le
  have hpR : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
  have hDreal : (1 : ℝ) < D := by exact_mod_cast hD
  let a : ℝ := max s (2 + (eps (n + 1) : ℝ))
  have ha2 : 2 ≤ a := by
    have hm := le_max_right s (2 + (eps (n + 1) : ℝ))
    have he : (0 : ℝ) ≤ eps (n + 1) := Nat.cast_nonneg _
    dsimp [a]; linarith
  have ha : 0 < a := by linarith
  have hgeometry := actual_source_carrier_geometry hn hD hs hp
  have hpv : (p : ℝ) < (D : ℝ) ^ (1 / a) := hgeometry.2
  have hcoord : a < log (D : ℝ) / log p := by
    have hv := SuzukiPowerCoordinates.coordinate_at_upper hDreal ha (rfl :
      (D : ℝ) ^ (1 / a) = (D : ℝ) ^ (1 / a))
    rw [← hv]
    exact div_lt_div_of_pos_left (log_pos hDreal) (log_pos hpR)
      (log_lt_log (by positivity) hpv)
  have hpSquare : p ^ 2 < D := natural_power_lt_of_lt_root (by omega) (by norm_num)
    (hpv.trans_le (rpow_one_div_mono_of_le hDreal.le (by norm_num) ha2))
  have hDp : 2 * p ≤ D := by nlinarith
  have hq : 2 ≤ D ⌈/⌉ p := ceilDiv_ge_threshold_of_scale hpPrime.pos hDp
  have hcoords := (coordinate_bounds hp2 hDp).1
  have hpar := eps_succ_add n
  have hparR : (eps (n + 1) : ℝ) + eps n = 1 := by exact_mod_cast hpar
  have hclosed : inheritedCoordinate D p ∈ closedDomain 2 n := by
    change (2 : ℝ) - (eps n : ℝ) ≤ log (D : ℝ) / log p - 1
    have hmax : 2 + (eps (n + 1) : ℝ) ≤ a := le_max_right _ _
    linarith
  have hclosed' : recursiveCoordinate D p ∈ closedDomain 2 n := by
    change (2 : ℝ) - (eps n : ℝ) ≤ recursiveCoordinate D p
    exact (show (2 : ℝ) - (eps n : ℝ) ≤ inheritedCoordinate D p from hclosed).trans hcoords
  have hid := recursiveCoordinate_power_identity hp2 hq
  have hh := hIH (D ⌈/⌉ p) p (recursiveCoordinate D p) (by omega) hclosed' (by rw [hid]; simp)
  rw [hid, ← sourceEuler_eq_real_product] at hh
  have henv := sourceLayerEnvelope_antitone n hε hclosed hclosed' hcoords
  have htest : sourceLayerTest n ε (log (D : ℝ) / log p) =
      sourceLayerEnvelope n ε (inheritedCoordinate D p) := by
    apply sourceLayerTest_eq
    have hmax : 2 + (eps (n + 1) : ℝ) ≤ a := le_max_right _ _
    linarith
  rw [htest]
  apply hh.trans
  exact mul_le_mul_of_nonneg_left henv (by rw [sourceEuler_eq_real_product]; exact (suzukiVProduct_pos S p).le)

#print axioms actual_source_inner_transport
end ChenEffective
