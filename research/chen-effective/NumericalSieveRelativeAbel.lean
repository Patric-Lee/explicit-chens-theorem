import NumericalSieveKernel
import MathlibNt.SieveTheory.Switching.SuzukiPrimeSums
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma87DimensionOne

namespace ChenEffective
open Real Set Finset MeasureTheory intervalIntegral
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.LinearSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Relative-product Abel bound on the actual finite prime atoms. No generic
Suzuki K, absolute error estimate, or unspecified asymptotic constant occurs. -/
theorem sieve_relative_prime_sum
    {S : BoundingSieve} {D w z s σ ε : ℝ} {H : ℝ → ℝ}
    (hD : 1 < D) (hw : 1 < w) (hwz : w ≤ z)
    (hs : 0 < s) (hsσ : s ≤ σ)
    (hz : z = D ^ (1 / s)) (hwcoord : w = D ^ (1 / σ))
    (hε : 0 ≤ ε) (hHcont : Continuous H)
    (hHnonneg : ∀ t ∈ Icc s σ, 0 ≤ H t)
    (hHanti : AntitoneOn H (Icc s σ))
    (hrelative : ∀ x ∈ Icc w z,
      suzukiLocalRatio S x z ≤ (1 + ε) * (log z / log x)) :
    suzukiLemmaEightSixPrimeSum S D w z H ≤
      ((1 + ε) / s) * (∫ t in s..σ, H t) + ε * H s := by
  let t := fun x : ℝ => log D / log x
  let g := fun x => H (t x)
  let M := finiteNodeLogRatio z
  let R := fun x => suzukiLocalRatio S x z
  have hcoord : ∀ x ∈ Icc w z, t x ∈ Icc s σ := by
    intro x hx
    exact SuzukiPowerCoordinates.log_div_log_mem_Icc hD hs hsσ hz hwcoord hx
  have hnodes : ∀ x ∈ suzukiFiniteNodes S w z, x ∈ Icc w z :=
    fun x hx => mem_suzukiFiniteNodes_Icc hwz hx
  have hpair := suzukiFiniteNodes_pairwise S hwz
  have hg : MonotoneOn g (Icc w z) := by
    intro x hx y hy hxy
    apply hHanti (hcoord y hy) (hcoord x hx)
    dsimp [t]
    apply div_le_div_of_nonneg_left (log_pos hD).le (log_pos (hw.trans_le hx.1))
    exact log_le_log (zero_lt_one.trans (hw.trans_le hx.1)) hxy
  have hvar : finiteNodeVariationSum R g (suzukiFiniteNodes S w z) ≤
      (1 + ε) * finiteNodeVariationSum M g (suzukiFiniteNodes S w z) := by
    rw [← finiteNodeVariationSum_smul_left]
    apply finiteNodeVariationSum_mono_of_pairwise
    apply pairwise_imp_of_mem hpair
    intro x hx y hy hxy
    have hdiff : 0 ≤ g y - g x := sub_nonneg.mpr (hg (hnodes x hx) (hnodes y hy) hxy)
    exact mul_le_mul_of_nonneg_right (hrelative y (hnodes y hy)) hdiff
  have hwg : 0 ≤ g w := hHnonneg _ (hcoord w ⟨le_rfl, hwz⟩)
  have hedge : R w * g w ≤ (1 + ε) * (M w * g w) := by
    have hh := mul_le_mul_of_nonneg_right (hrelative w ⟨le_rfl, hwz⟩) hwg
    simpa only [R, M, finiteNodeLogRatio, mul_assoc] using hh
  have hM := finiteNodeMainRatio_boundary_variation w z z
    (suzukiSupportedPrimeNodes S w z) g
  have hz1 : 1 < z := hw.trans_le hwz
  have hlz : log z ≠ 0 := (log_pos hz1).ne'
  have hMself : finiteNodeLogRatio z z = 1 := by unfold finiteNodeLogRatio; exact div_self hlz
  rw [hMself, one_mul] at hM
  change M w * g w - g z + finiteNodeVariationSum M g (suzukiFiniteNodes S w z) =
    finiteNodeMainRatioSum z g (suzukiFiniteNodes S w z) at hM
  have hab := suzukiFiniteNodeAbel_atoms S w z g
  have hprime := suzukiFiniteNodeAtomSum_eq_lemmaEightSixPrimeSum S D w z H hwz
  have hatoms : suzukiLemmaEightSixPrimeSum S D w z H ≤
      (1 + ε) * finiteNodeMainRatioSum z g (suzukiFiniteNodes S w z) + ε * g z := by
    rw [← hprime, hab]
    change R w * g w - g z + finiteNodeVariationSum R g (suzukiFiniteNodes S w z) ≤ _
    rw [← hM]
    nlinarith only [hedge, hvar]
  have hmain := finiteNodeMainRatioSum_le_integral g
    (suzukiSupportedPrimeNodes S w z) hw hwz hpair hg
  have hchange := SuzukiMainTermNormalization.stieltjesMainTerm_changeOfVariables
    (D := D) (w := w) (z := z) (s := s) (σ := σ) (H := H)
    hD hs hsσ hz hwcoord hHcont
  rw [hchange] at hmain
  change finiteNodeMainRatioSum z g (suzukiFiniteNodes S w z) ≤ _ at hmain
  have hendpoint : g z = H s := by
    dsimp [g, t]
    rw [SuzukiPowerCoordinates.coordinate_at_upper hD hs hz]
  rw [hendpoint] at hatoms
  have hh := mul_le_mul_of_nonneg_left hmain (by linarith : 0 ≤ 1 + ε)
  calc
    _ ≤ (1 + ε) * finiteNodeMainRatioSum z g (suzukiFiniteNodes S w z) + ε * H s := hatoms
    _ ≤ (1 + ε) * (1 / s * ∫ t in s..σ, H t) + ε * H s := add_le_add hh le_rfl
    _ = _ := by ring

#print axioms sieve_relative_prime_sum

theorem sieve_relative_middle_prime_sum
    {S : BoundingSieve} {D w v z s a σ ε : ℝ} {H : ℝ → ℝ}
    (hD : 1 < D) (hw : 1 < w) (hwv : w ≤ v) (hvz : v ≤ z)
    (hs : 0 < s) (ha : 0 < a) (haσ : a ≤ σ)
    (hz : z = D ^ (1 / s)) (hv : v = D ^ (1 / a)) (hwcoord : w = D ^ (1 / σ))
    (hε : 0 ≤ ε) (hHcont : Continuous H)
    (hHnonneg : ∀ t ∈ Icc a σ, 0 ≤ H t) (hHanti : AntitoneOn H (Icc a σ))
    (hrelative : ∀ u r : ℝ, 1 < u → u ≤ r →
      suzukiLocalRatio S u r ≤ (1 + ε) * (log r / log u)) :
    suzukiLemmaEightSevenPrimeSum S D w v z H ≤
      ((1 + ε) ^ 2 / s) * (∫ t in a..σ, H t) +
        (1 + ε) * ε * (a / s) * H a := by
  have hbase := sieve_relative_prime_sum hD hw hwv ha haσ hv hwcoord hε hHcont
    hHnonneg hHanti (fun x hx => hrelative x v (hw.trans_le hx.1) hx.2)
  have hR := hrelative v z (hw.trans_le hwv) hvz
  have hratio : log z / log v = a / s := by
    rw [hz, hv, log_rpow (by linarith : 0 < D), log_rpow (by linarith : 0 < D)]
    field_simp [(log_pos hD).ne', hs.ne', ha.ne']
  rw [hratio] at hR
  have hbound : 0 ≤ ((1 + ε) / a) * (∫ t in a..σ, H t) + ε * H a := by
    have hI := intervalIntegral.integral_nonneg (μ := volume) haσ hHnonneg
    have hHa := hHnonneg a ⟨le_rfl, haσ⟩
    positivity
  have hR0 : 0 ≤ suzukiLocalRatio S v z := by
    unfold suzukiLocalRatio
    apply Finset.prod_nonneg
    intro p hp
    have hP := (mem_filter.mp hp).1
    exact inv_nonneg.mpr (sub_nonneg.mpr (S.nu_lt_one_of_prime p
      (Nat.prime_of_mem_primeFactors hP) (Nat.dvd_of_mem_primeFactors hP)).le)
  rw [suzukiLemmaEightSevenPrimeSum_eq_localRatio_mul S D w v z H hvz]
  calc
    _ ≤ suzukiLocalRatio S v z *
        (((1 + ε) / a) * (∫ t in a..σ, H t) + ε * H a) :=
      mul_le_mul_of_nonneg_left hbase hR0
    _ ≤ ((1 + ε) * (a / s)) *
        (((1 + ε) / a) * (∫ t in a..σ, H t) + ε * H a) :=
      mul_le_mul_of_nonneg_right hR hbound
    _ = _ := by field_simp

#print axioms sieve_relative_middle_prime_sum
end ChenEffective
