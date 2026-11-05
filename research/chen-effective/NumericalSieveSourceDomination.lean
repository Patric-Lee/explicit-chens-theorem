import NumericalSieveLayerDecay
import NumericalSieveRelativeAbel
import NumericalSieveKernelRecurrence
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiRoundedBaseOne
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma143NatCeilSupport

namespace ChenEffective
open Real Set Finset MeasureTheory intervalIntegral
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open KappaOneModel
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def HasRelativeSieveProduct (S : BoundingSieve) (ε : ℝ) : Prop :=
  ∀ u z : ℝ, 1 < u → u ≤ z →
    suzukiLocalRatio S u z ≤ (1 + ε) * (log z / log u)

theorem actual_source_base_domination {S : BoundingSieve} {D z : ℕ} {s ε : ℝ}
    (hD : 1 < D) (hs : 1 ≤ s) (hε : 0 ≤ ε) (hrelative : HasRelativeSieveProduct S ε)
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    suzukiSourceV S 1 D z ≤ suzukiVProduct S ((D : ℝ) ^ (1 / s)) *
      (layer 2 1 s + ε * kernelSieveError 0 * exp 2 * sieveHat s) := by
  have hs0 : 0 < s := by linarith
  have hDr : 1 < (D : ℝ) := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < D := by linarith
  have hV := (suzukiVProduct_pos S ((D : ℝ) ^ (1 / s))).le
  have hhat := (sieveHat_pos s).le
  by_cases hs3 : 3 ≤ s
  · rw [suzukiSourceV_eq_zero_below_natCeil_rpow S hD (by linarith : 2 ≤ s) hz
      (by apply Nat.le_floor; norm_num only [Nat.cast_one]; linarith)]
    have hreg := (regular (by norm_num : (1 : ℝ) < 2) 1).nonneg s
      (show s ∈ closedDomain 2 1 by simp only [closedDomain, Set.mem_Ici, eps]; norm_num; linarith)
    have hK := kernelSieveError_nonneg 0
    positivity
  have hs3' : s ≤ 3 := le_of_not_ge hs3
  let x : ℝ := (D : ℝ) ^ (1 / s)
  let w : ℝ := (D : ℝ) ^ (1 / 3 : ℝ)
  have hw1 : 1 < w := one_lt_rpow hDr (by norm_num)
  have hwx : w ≤ x := rpow_one_div_mono_of_le hDr.le hs0 hs3'
  have hR := hrelative w x hw1 hwx
  have hratio : log x / log w = 3 / s := by
    dsimp [x, w]
    rw [log_rpow hD0, log_rpow hD0]
    field_simp [(log_pos hDr).ne', hs0.ne']
  rw [hratio] at hR
  have hbase : layer 2 1 s = (3 - s) / s := by
    simp only [layer, show (2 : ℝ) + 1 = 3 by norm_num, min_eq_left hs3',
      intervalIntegral.integral_const, smul_eq_mul, mul_one]
    rw [div_eq_inv_mul]
  have hhatbound : 3 / s ≤ 3 * exp 2 * sieveHat s := by
    have hh := mul_le_mul_of_nonneg_left (sieveHat_weighted_compact hs hs3')
      (show 0 ≤ 3 * exp (2 : ℝ) by positivity)
    have he : 3 * exp (2 : ℝ) * exp (-2) = 3 := by
      rw [mul_assoc, ← exp_add]; norm_num
    rw [he] at hh
    apply (div_le_iff₀ hs0).mpr
    nlinarith only [hh]
  rw [roundedBaseOne_sourceV_one_eq_realVOne S hz, suzukiVOne,
    suzukiVOneNormalized_eq_localRatio_sub_one S (D : ℝ) 2 x
      (by simpa only [suzukiYOne_two] using hwx)]
  rw [suzukiYOne_two]
  change suzukiVProduct S x * (suzukiLocalRatio S w x - 1) ≤ _
  apply mul_le_mul_of_nonneg_left _ hV
  rw [hbase]
  norm_num only [kernelSieveError]
  have hh := mul_le_mul_of_nonneg_left hhatbound hε
  have hid : (1 + ε) * (3 / s) - 1 = (3 - s) / s + ε * (3 / s) := by
    field_simp; ring
  have hraw := sub_le_sub_right hR 1
  rw [hid] at hraw
  nlinarith only [hraw, hh]

#print axioms actual_source_base_domination

noncomputable def sourceLayerEnvelope (n : ℕ) (ε u : ℝ) : ℝ :=
  layer 2 n u + ε * kernelSieveError (n - 1) * exp 2 * sieveHat u

theorem sourceLayerEnvelope_nonneg (n : ℕ) {ε u : ℝ} (hε : 0 ≤ ε)
    (hu : u ∈ closedDomain 2 n) : 0 ≤ sourceLayerEnvelope n ε u := by
  have hf := (regular (by norm_num : (1 : ℝ) < 2) n).nonneg u hu
  have ht := kernelSieveError_nonneg (n - 1)
  have hh := (sieveHat_pos u).le
  unfold sourceLayerEnvelope
  positivity

theorem sourceLayerEnvelope_antitone (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    AntitoneOn (sourceLayerEnvelope n ε) (closedDomain 2 n) := by
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
    (show 0 ≤ ε * kernelSieveError (n - 1) * exp 2 from
      mul_nonneg (mul_nonneg hε (kernelSieveError_nonneg _)) (exp_pos _).le)
  exact add_le_add hf hh

noncomputable def sourceLayerTest (n : ℕ) (ε t : ℝ) : ℝ :=
  sourceLayerEnvelope n ε (max (2 - (eps n : ℝ)) (t - 1))

theorem sourceLayerTest_continuous (n : ℕ) (ε : ℝ) : Continuous (sourceLayerTest n ε) := by
  let c : ℝ → ℝ := fun t => max (2 - (eps n : ℝ)) (t - 1)
  have hc : Continuous c := continuous_const.max (continuous_id.sub continuous_const)
  have hf : Continuous (fun t => layer 2 n (c t)) := by
    apply (regular (by norm_num : (1 : ℝ) < 2) n).continuous.comp_continuous hc
    intro t
    change (2 : ℝ) - (eps n : ℝ) ≤ c t
    exact le_max_left _ _
  change Continuous (fun t => layer 2 n (c t) +
    ε * kernelSieveError (n - 1) * exp 2 * sieveHat (c t))
  exact hf.add (continuous_const.mul (sieveHat_continuous.comp hc))

theorem sourceLayerTest_nonneg (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    0 ≤ sourceLayerTest n ε t := by
  apply sourceLayerEnvelope_nonneg n hε
  change (2 : ℝ) - (eps n : ℝ) ≤ max (2 - (eps n : ℝ)) (t - 1)
  exact le_max_left _ _

theorem sourceLayerTest_antitone (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    Antitone (sourceLayerTest n ε) := by
  intro x y hxy
  apply sourceLayerEnvelope_antitone n hε
  · change (2 : ℝ) - (eps n : ℝ) ≤ max (2 - (eps n : ℝ)) (x - 1)
    exact le_max_left _ _
  · change (2 : ℝ) - (eps n : ℝ) ≤ max (2 - (eps n : ℝ)) (y - 1)
    exact le_max_left _ _
  · exact max_le_max_left _ (sub_le_sub_right hxy 1)

theorem sourceLayerTest_eq (n : ℕ) (ε : ℝ) {t : ℝ}
    (ht : 3 - (eps n : ℝ) ≤ t) :
    sourceLayerTest n ε t = sourceLayerEnvelope n ε (t - 1) := by
  unfold sourceLayerTest
  rw [max_eq_right (by linarith)]
end ChenEffective
