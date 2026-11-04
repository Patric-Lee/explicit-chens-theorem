import NumericalMixedCaseIITransfer
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiRoundedBaseOne

open scoped Classical BigOperators Interval
namespace ChenEffective
variable [profile : CorrectionProfile]
open Real Set Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open SuzukiFiniteContinuousLayers SuzukiLemma144KappaOne SuzukiLemma144Equation1410
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000

theorem mixed_caseII_from_cube (S : BoundingSieve) (H : Section13HatLayers)
    (hH : Section13HatSourceContract H) {C K s : ℝ} {N D : ℕ}
    (hC : 1 ≤ C) (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K)
    (hN : Odd N) (hN3 : 3 ≤ N) (hD : 2 ≤ D) (hs : 1 < s) (hs3 : s ≤ 3)
    (hσ : 3 ≤ sourceSigma (D : ℝ) 16)
    (hcut : (logPowerCutoff 32 : ℝ) ≤ Real.log D) (hKlevel : K ^ (7 : ℝ) ≤ Real.log D)
    (hcube : suzukiActualT S N D ⌈(D : ℝ) ^ (1 / (3 : ℝ))⌉₊ ≤
      suzukiVProduct S (⌈(D : ℝ) ^ (1 / (3 : ℝ))⌉₊ : ℝ) * finiteSourceLayer 1 2 N 3 +
        (1 - 1 / (10 * sourceSigma (D : ℝ) 16)) * mixedBudget S H N D
          ⌈(D : ℝ) ^ (1 / (3 : ℝ))⌉₊ C K 16 (1 / 2) 3) :
    suzukiActualT S N D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
      suzukiVProduct S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) *
        (finiteSourceLayer 1 2 N s + C * Real.exp (Real.sqrt K) * mixedError H N D 16 (1 / 2) s) := by
  let yr := (D : ℝ) ^ (1 / (3 : ℝ))
  let zr := (D : ℝ) ^ (1 / s)
  let y := ⌈yr⌉₊
  let z := ⌈zr⌉₊
  let L := Real.log (D : ℝ)
  let σ := sourceSigma (D : ℝ) 16
  let r := 1 - 1 / (10 * σ)
  let P := C * Real.exp (Real.sqrt K)
  let γ := (3 / s) * (1 + 3 * K / L)
  have hD1 : (1 : ℝ) < D := by exact_mod_cast (show 1 < D by omega)
  have hD0 : (0 : ℝ) < D := zero_lt_one.trans hD1
  have hL0 : 0 < L := Real.log_pos hD1
  have hL9 : 9 ≤ L := real_log_power_cutoff_nine hcut
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hs0 : 0 < s := zero_lt_one.trans hs
  have hσ0 : 0 < σ := by dsimp [σ]; linarith only [hσ]
  have hr0 : 0 ≤ r := by
    have hh : 1 / (10 * σ) ≤ 1 := (div_le_one (by positivity)).mpr (by dsimp [σ]; linarith only [hσ])
    dsimp [r]
    linarith only [hh]
  have hP : 1 ≤ P := by
    have he := Real.one_le_exp (Real.sqrt_nonneg K)
    dsimp [P]
    nlinarith only [mul_le_mul hC he (by norm_num : (0 : ℝ) ≤ 1) (by linarith only [hC] : 0 ≤ C)]
  have hrealorder : yr ≤ zr := by
    unfold yr zr
    exact Real.rpow_le_rpow_of_exponent_le hD1.le
      (one_div_le_one_div_of_le hs0 hs3)
  have hyz : y ≤ z := Nat.ceil_mono hrealorder
  have hyr0 : 0 < yr := Real.rpow_pos_of_pos hD0 _
  have hzr0 : 0 < zr := Real.rpow_pos_of_pos hD0 _
  have hyr2 : 2 ≤ yr := by
    have hD8 : (8 : ℝ) ≤ D := by
      have hh := Real.log_le_sub_one_of_pos hD0
      change 9 ≤ Real.log (D : ℝ) at hL9
      linarith only [hh, hL9]
    unfold yr
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num : (0 : ℝ) ≤ 2) hD0.le
      (by norm_num : (0 : ℝ) < 3)).mpr
    norm_num
    exact_mod_cast hD8
  have hzr2 : 2 ≤ zr := hyr2.trans hrealorder
  have hVy : suzukiVProduct S (y : ℝ) = suzukiVProduct S yr := suzukiVProduct_natCeil_eq_power S hyr0 rfl
  have hVz : suzukiVProduct S (z : ℝ) = suzukiVProduct S zr := suzukiVProduct_natCeil_eq_power S hzr0 rfl
  have hratio : suzukiVProduct S (y : ℝ) ≤ suzukiVProduct S (z : ℝ) * γ := by
    have hh := hlocal yr zr hyr2 hrealorder
    have heq : Real.log zr / Real.log yr * (1 + K / Real.log yr) = γ := by
      unfold yr zr γ L
      rw [Real.log_rpow hD0, Real.log_rpow hD0]
      field_simp [(Real.log_pos hD1).ne', hs0.ne']
    change suzukiLocalRatio S yr zr ≤ _ at hh
    rw [heq, ← mixed_V_ratio S hrealorder, ← hVy, ← hVz] at hh
    have hp := (div_le_iff₀ (suzukiVProduct_pos S (z : ℝ))).mp hh
    simpa only [mul_comm] using hp
  have hF0 : 0 ≤ finiteSourceLayer 1 2 N 3 :=
    finiteSourceLayer_nonneg_on_parityDomain (by norm_num) N (by
      norm_num [KappaOneModel.parityDomain, Nat.odd_iff.mp hN])
  have hF : finiteSourceLayer 1 2 N 3 ≤ 864 :=
    (numerical_caseII_endpoint_layers hH N hN hN3).1
  have hA3 := mixedError_nonneg hH.toSection13HatContract (d := (16 : ℝ))
    (Δ := (1 / 2 : ℝ)) hD1 (by norm_num : (0 : ℝ) < 3) N
  have hB0 : 0 ≤ finiteSourceLayer 1 2 N 3 + P * r * mixedError H N D 16 (1 / 2) 3 := by positivity
  have hcub : suzukiActualT S N D y ≤
      suzukiVProduct S (z : ℝ) * γ * (finiteSourceLayer 1 2 N 3 + P * r * mixedError H N D 16 (1 / 2) 3) := by
    apply hcube.trans
    calc
      _ = suzukiVProduct S (y : ℝ) * (finiteSourceLayer 1 2 N 3 + P * r * mixedError H N D 16 (1 / 2) 3) := by
        unfold mixedBudget P
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hratio hB0
  have hbase := suzukiSourceV_one_le_V_natCeil_mul_fOne_add_localError
    (S := S) (D := D) (z := z) rfl hD1 hs0 hs3 hzr2 hK0 hlocal
  have hbracket := natCeil_cuberoot_cubeBracket D (by omega : 0 < D)
  have hT : suzukiActualT S N D z = suzukiActualT S N D y + suzukiSourceV S 1 D z := by
    have hh := suzukiSourceParitySum_caseII_cut_of_ceilingCube S hN hyz hbracket.1 hbracket.2
    simpa only [sourceParityIndices_eq_actualParityCarrier, ← suzukiActualT_eq_parity_sum] using hh
  have hroot := mixed_gate_power_large hcut
  have hQ : mixedCubicPerturbation ≤ L := by
    have hp : L ^ (1 / 8 : ℝ) ≤ L := Real.rpow_le_self_of_one_le (by linarith only [hL9]) (by norm_num)
    have hh := hroot.trans hp
    norm_num [mixedCubicPerturbation] at hh ⊢
    linarith only [hh]
  have h3 : (3 : ℝ) ^ (16 : ℝ) ≤ L := by
    norm_num [mixedCubicPerturbation] at hQ ⊢
    linarith only [hQ]
  have hA : (1 / 3 : ℝ) * L ^ (-(1 / 2 : ℝ)) ≤ mixedError H N D 16 (1 / 2) s := by
    have hh := mul_le_mul_of_nonneg_right (one_third_le_errorEnvelope_caseII (d := (16 : ℝ)) hH.toSection13HatContract hN hD1 hs hs3)
      (Real.rpow_nonneg hL0.le (-(1 / 2 : ℝ)))
    have hb := polynomialCorrectionWeight_pos.le
    have hp : 0 ≤ polynomialCorrection (D : ℝ) s := by unfold polynomialCorrection; positivity
    unfold mixedError
    nlinarith only [hh, mul_nonneg hb hp]
  have hscalar := mixed_caseII_scalar (by linarith only [hL9] : 1 ≤ L) hσ hK hs hQ
    (mixed_caseII_small_parameter hD1 hcut hK hKlevel) hF hA hP
    (mixed_cubic_error_transfer hH.toSection13HatContract hN hD1 hs0 hs3 h3)
  have hfinite := finiteSourceLayer_caseII_identity (β := (2 : ℝ)) hN hs0 (by norm_num at hs3 ⊢; exact hs3)
  rw [hT]
  apply (add_le_add hcub hbase).trans
  have hh := mul_le_mul_of_nonneg_left hscalar (suzukiVProduct_pos S (z : ℝ)).le
  have hfiniteV := congrArg (fun a : ℝ => suzukiVProduct S (z : ℝ) * a) hfinite
  norm_num only [show (2 : ℝ) + 1 = 3 by norm_num] at hfiniteV
  dsimp [γ, P, r, σ, L, z, zr] at hh hfiniteV ⊢
  nlinarith only [hh, hfiniteV]

#print axioms mixed_caseII_from_cube
end ChenEffective
