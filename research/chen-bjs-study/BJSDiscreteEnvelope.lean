import BJSParitySums
import BJSSharpRecurrence
import NumericalSieveSourceGeometry

noncomputable section
namespace ChenEffective
open Real Set Finset MeasureTheory intervalIntegral
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers KappaOneModel
open SuzukiLemma144Equation1410
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable def bjsLayerEnvelope (n : ℕ) (ε u : ℝ) : ℝ :=
  layer 2 n u + ε * bjsSharpError (n - 1) * exp 2 * sieveHat u

theorem bjsLayerEnvelope_nonneg (n : ℕ) {ε u : ℝ} (hε : 0 ≤ ε)
    (hu : u ∈ closedDomain 2 n) : 0 ≤ bjsLayerEnvelope n ε u := by
  have hf := (regular (by norm_num : (1 : ℝ) < 2) n).nonneg u hu
  have ht := bjsSharpError_nonneg (n - 1)
  have hh := (sieveHat_pos u).le
  unfold bjsLayerEnvelope
  positivity

theorem bjsLayerEnvelope_antitone (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    AntitoneOn (bjsLayerEnvelope n ε) (closedDomain 2 n) := by
  intro x hx y hy hxy
  have hreg := regular (by norm_num : (1 : ℝ) < 2) n
  have hw := hreg.weighted_antitone hx hy hxy
  have hfy := hreg.nonneg y hy
  have hx0 := closedDomain_pos (by norm_num : (1 : ℝ) < 2) hx
  have hf : layer 2 n y ≤ layer 2 n x := by
    have hh : x * layer 2 n y ≤ x * layer 2 n x :=
      (mul_le_mul_of_nonneg_right hxy hfy).trans hw
    exact le_of_mul_le_mul_left hh hx0
  have hh := mul_le_mul_of_nonneg_left (sieveHat_antitone hxy)
    (show 0 ≤ ε * bjsSharpError (n - 1) * exp 2 from
      mul_nonneg (mul_nonneg hε (bjsSharpError_nonneg _)) (exp_pos _).le)
  exact add_le_add hf hh

noncomputable def bjsLayerTest (n : ℕ) (ε t : ℝ) : ℝ :=
  bjsLayerEnvelope n ε (max (2 - (eps n : ℝ)) (t - 1))

theorem bjsLayerTest_continuous (n : ℕ) (ε : ℝ) : Continuous (bjsLayerTest n ε) := by
  let c : ℝ → ℝ := fun t => max (2 - (eps n : ℝ)) (t - 1)
  have hc : Continuous c := continuous_const.max (continuous_id.sub continuous_const)
  have hf : Continuous (fun t => layer 2 n (c t)) := by
    apply (regular (by norm_num : (1 : ℝ) < 2) n).continuous.comp_continuous hc
    intro t
    change (2 : ℝ) - (eps n : ℝ) ≤ c t
    exact le_max_left _ _
  change Continuous (fun t => layer 2 n (c t) +
    ε * bjsSharpError (n - 1) * exp 2 * sieveHat (c t))
  exact hf.add (continuous_const.mul (sieveHat_continuous.comp hc))

theorem bjsLayerTest_nonneg (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    0 ≤ bjsLayerTest n ε t := by
  apply bjsLayerEnvelope_nonneg n hε
  change (2 : ℝ) - (eps n : ℝ) ≤ max (2 - (eps n : ℝ)) (t - 1)
  exact le_max_left _ _

theorem bjsLayerTest_antitone (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    Antitone (bjsLayerTest n ε) := by
  intro x y hxy
  apply bjsLayerEnvelope_antitone n hε
  · change (2 : ℝ) - (eps n : ℝ) ≤ max (2 - (eps n : ℝ)) (x - 1)
    exact le_max_left _ _
  · change (2 : ℝ) - (eps n : ℝ) ≤ max (2 - (eps n : ℝ)) (y - 1)
    exact le_max_left _ _
  · exact max_le_max_left _ (sub_le_sub_right hxy 1)

theorem bjsLayerTest_eq (n : ℕ) (ε : ℝ) {t : ℝ}
    (ht : 3 - (eps n : ℝ) ≤ t) :
    bjsLayerTest n ε t = bjsLayerEnvelope n ε (t - 1) := by
  unfold bjsLayerTest
  rw [max_eq_right (by linarith)]
theorem bjs_actual_source_inner_transport {S : BoundingSieve} {n D p : ℕ} {s ε : ℝ}
    (hn : 0 < n) (hD : 1 < D) (hε : 0 ≤ ε) (hs : s ∈ closedDomain 2 (n + 1))
    (hp : p ∈ suzukiSourceOuterCarrierPowerReal (n + 1) D
      ((D : ℝ) ^ (1 / s)) S.prodPrimes.primeFactors)
    (hIH : ∀ D' z' : ℕ, ∀ s' : ℝ, 1 < D' → s' ∈ closedDomain 2 n →
      z' = ⌈(D' : ℝ) ^ (1 / s')⌉₊ →
      suzukiSourceV S n D' z' ≤ suzukiVProduct S ((D' : ℝ) ^ (1 / s')) *
        bjsLayerEnvelope n ε s') :
    suzukiSourceV S n (D ⌈/⌉ p) p ≤ sourceDiscreteEuler S p *
      bjsLayerTest n ε (log (D : ℝ) / log p) := by
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
  have henv := bjsLayerEnvelope_antitone n hε hclosed hclosed' hcoords
  have htest : bjsLayerTest n ε (log (D : ℝ) / log p) =
      bjsLayerEnvelope n ε (inheritedCoordinate D p) := by
    apply bjsLayerTest_eq
    have hmax : 2 + (eps (n + 1) : ℝ) ≤ a := le_max_right _ _
    linarith
  rw [htest]
  apply hh.trans
  exact mul_le_mul_of_nonneg_left henv (by rw [sourceEuler_eq_real_product]; exact (suzukiVProduct_pos S p).le)

#print axioms bjs_actual_source_inner_transport

theorem bjs_actual_source_base {S : BoundingSieve} {D z : ℕ} {s ε : ℝ}
    (hD : 1 < D) (hs : 1 ≤ s) (hε : 0 ≤ ε) (hrelative : HasRelativeSieveProduct S ε)
    (hz : z=⌈(D : ℝ)^(1/s)⌉₊) :
    suzukiSourceV S 1 D z ≤ suzukiVProduct S ((D : ℝ)^(1/s))*bjsLayerEnvelope 1 ε s := by
  simpa only [bjsLayerEnvelope,Nat.reduceSub,bjsSharpError,kernelSieveError] using
    actual_source_base_domination hD hs hε hrelative hz

#print axioms bjs_actual_source_base
end ChenEffective
