import NumericalSourceRatio
import NumericalCompactDerivative

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
private lemma shifted_slope_le_log
    {D d t : ℝ} (hlog : 0 < Real.log D) (hd : 0 ≤ d) (ht : 0 < t) :
    perturbationSlope D d 1 t ≤
      (d + 1) * Real.log (1 + (t + 1) ^ d / Real.log D) := by
  let u : ℝ := (t + 1) ^ d / Real.log D
  have htp : 0 < t + 1 := by linarith
  have hu0 : 0 ≤ u :=
    div_nonneg (Real.rpow_nonneg htp.le _) hlog.le
  have hb : 0 < 1 + u := by linarith
  have hulog : u / (1 + u) ≤ Real.log (1 + u) := by
    have hi := Real.log_le_sub_one_of_pos (inv_pos.mpr hb)
    rw [Real.log_inv] at hi
    have heq : u / (1 + u) = 1 - (1 + u)⁻¹ := by
      field_simp [hb.ne']
      ring
    rw [heq]
    linarith
  have hpow : (t + 1) * (t + 1) ^ (d - 1) = (t + 1) ^ d := by
    calc
      (t + 1) * (t + 1) ^ (d - 1) =
          (t + 1) ^ (1 : ℝ) * (t + 1) ^ (d - 1) := by rw [Real.rpow_one]
      _ = (t + 1) ^ ((1 : ℝ) + (d - 1)) :=
        (Real.rpow_add htp _ _).symm
      _ = (t + 1) ^ d := by ring_nf
  have hnum :
      t * (d * (t + 1) ^ (d - 1) / Real.log D) ≤ d * u := by
    have hfac : 0 ≤ d * (t + 1) ^ (d - 1) / Real.log D :=
      div_nonneg (mul_nonneg hd (Real.rpow_nonneg htp.le _)) hlog.le
    calc
      t * (d * (t + 1) ^ (d - 1) / Real.log D) ≤
          (t + 1) * (d * (t + 1) ^ (d - 1) / Real.log D) := by
            exact mul_le_mul_of_nonneg_right (by linarith) hfac
      _ = d * u := by
        dsimp [u]
        rw [show (t + 1) * (d * (t + 1) ^ (d - 1) / Real.log D) =
          d * ((t + 1) * (t + 1) ^ (d - 1)) / Real.log D by ring, hpow]
        ring
  have hterm :
      t * (d * (t + 1) ^ (d - 1) / Real.log D) / (1 + u) ≤
        d * (u / (1 + u)) := by
    rw [show d * (u / (1 + u)) = (d * u) / (1 + u) by ring]
    exact (div_le_div_iff_of_pos_right hb).2 hnum
  rw [perturbationSlope]
  change Real.log (1 + u) +
      t * (d * (t + 1) ^ (d - 1) / Real.log D) / (1 + u) ≤ _
  calc
    Real.log (1 + u) +
        t * (d * (t + 1) ^ (d - 1) / Real.log D) / (1 + u) ≤
      Real.log (1 + u) + d * (u / (1 + u)) := add_le_add_right hterm _
    _ ≤ Real.log (1 + u) + d * Real.log (1 + u) := by gcongr
    _ = (d + 1) * Real.log (1 + u) := by ring

private lemma shifted_log_le_two_max
    {D d t : ℝ} (hlog : 0 < Real.log D) (hd : 0 < d)
    (ht : 0 < t) (hdt : d ≤ t) :
    Real.log (1 + (t + 1) ^ d / Real.log D) ≤
      2 * max 1 (Real.log (1 + t ^ d / Real.log D)) := by
  let z : ℝ := t ^ d / Real.log D
  let r : ℝ := (t + 1) / t
  have hz0 : 0 ≤ z := div_nonneg (Real.rpow_nonneg ht.le _) hlog.le
  have hrpos : 0 < r := div_pos (by linarith) ht
  have hrone : 1 ≤ r := by
    dsimp [r]
    apply (le_div_iff₀ ht).2
    linarith
  have hrform : r = 1 + 1 / t := by
    dsimp [r]
    field_simp [ne_of_gt ht]
  have hlogr : Real.log r ≤ 1 / t := by
    rw [hrform]
    have hp : 0 < 1 + 1 / t := by positivity
    linarith [Real.log_le_sub_one_of_pos hp]
  have hdtdiv : d / t ≤ 1 := (div_le_one ht).2 hdt
  have hdlog : d * Real.log r ≤ 1 := by
    have hd0 : 0 ≤ d := hd.le
    calc
      d * Real.log r ≤ d * (1 / t) := mul_le_mul_of_nonneg_left hlogr hd0
      _ = d / t := by ring
      _ ≤ 1 := hdtdiv
  have hrpow : r ^ d ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hrpos]
    exact Real.exp_le_exp.mpr (by simpa [mul_comm] using hdlog)
  have hpoweq : (t + 1) ^ d = t ^ d * r ^ d := by
    have htr : t * r = t + 1 := by
      dsimp [r]
      field_simp [ne_of_gt ht]
    rw [← Real.mul_rpow ht.le hrpos.le, htr]
  have hu : (t + 1) ^ d / Real.log D ≤ Real.exp 1 * z := by
    rw [hpoweq]
    dsimp [z]
    have htd0 : 0 ≤ t ^ d / Real.log D :=
      div_nonneg (Real.rpow_nonneg ht.le _) hlog.le
    calc
      (t ^ d * r ^ d) / Real.log D = (t ^ d / Real.log D) * r ^ d := by ring
      _ ≤ (t ^ d / Real.log D) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left hrpow htd0
      _ = Real.exp 1 * (t ^ d / Real.log D) := by ring
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hbase :
      1 + (t + 1) ^ d / Real.log D ≤ Real.exp 1 * (1 + z) := by
    calc
      1 + (t + 1) ^ d / Real.log D ≤ 1 + Real.exp 1 * z := by linarith
      _ ≤ Real.exp 1 + Real.exp 1 * z := by linarith
      _ = Real.exp 1 * (1 + z) := by ring
  have hleftpos : 0 < 1 + (t + 1) ^ d / Real.log D := by
    have : 0 ≤ (t + 1) ^ d / Real.log D :=
      div_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ t + 1) _) hlog.le
    linarith
  have hlogcmp : Real.log (1 + (t + 1) ^ d / Real.log D) ≤
      1 + Real.log (1 + z) := by
    have hm := Real.strictMonoOn_log.monotoneOn hleftpos
      (mul_pos (Real.exp_pos 1) (by linarith : 0 < 1 + z)) hbase
    rw [Real.log_mul (Real.exp_ne_zero 1) (by linarith : 1 + z ≠ 0), Real.log_exp] at hm
    exact hm
  have hmax1 : 1 ≤ max 1 (Real.log (1 + z)) := le_max_left _ _
  have hmaxlog : Real.log (1 + z) ≤ max 1 (Real.log (1 + z)) := le_max_right _ _
  calc
    Real.log (1 + (t + 1) ^ d / Real.log D) ≤ 1 + Real.log (1 + z) := hlogcmp
    _ ≤ 2 * max 1 (Real.log (1 + z)) := by linarith
    _ = 2 * max 1 (Real.log (1 + t ^ d / Real.log D)) := by rfl

private lemma both_slopes_le_ratio_coefficient
    {D d t : ℝ} (hlog : 0 < Real.log D) (hd : 0 < d)
    (ht : 0 < t) (hdt : d ≤ t) {ε : ℝ} (hε : ε = 0 ∨ ε = 1) :
    perturbationSlope D d ε t ≤
      2 * (d + 1) * max 1 (Real.log (1 + t ^ d / Real.log D)) := by
  rcases hε with rfl | rfl
  · have hs : perturbationSlope D d 0 t ≤
        (d + 1) * Real.log (1 + t ^ d / Real.log D) := by
      -- The unshifted logarithmic derivative is the standard `z/(1+z)` estimate.
      let z : ℝ := t ^ d / Real.log D
      have hz0 : 0 ≤ z := div_nonneg (Real.rpow_nonneg ht.le _) hlog.le
      have hb : 0 < 1 + z := by linarith
      have hzlog : z / (1 + z) ≤ Real.log (1 + z) := by
        have hi := Real.log_le_sub_one_of_pos (inv_pos.mpr hb)
        rw [Real.log_inv] at hi
        have heq : z / (1 + z) = 1 - (1 + z)⁻¹ := by
          field_simp [hb.ne']
          ring
        rw [heq]
        linarith
      have htpow : t * t ^ (d - 1) = t ^ d := by
        calc
          t * t ^ (d - 1) = t ^ (1 : ℝ) * t ^ (d - 1) := by rw [Real.rpow_one]
          _ = t ^ ((1 : ℝ) + (d - 1)) := (Real.rpow_add ht _ _).symm
          _ = t ^ d := by ring_nf
      have hterm : t * (d * t ^ (d - 1) / Real.log D) /
          (1 + t ^ d / Real.log D) = d * (z / (1 + z)) := by
        dsimp [z]
        rw [show t * (d * t ^ (d - 1) / Real.log D) =
          d * (t * t ^ (d - 1)) / Real.log D by ring, htpow]
        ring
      rw [perturbationSlope]
      simp only [add_zero]
      rw [hterm]
      calc
        Real.log (1 + z) + d * (z / (1 + z)) ≤
            Real.log (1 + z) + d * Real.log (1 + z) := by gcongr
        _ = (d + 1) * Real.log (1 + z) := by ring
    have hlogmax : Real.log (1 + t ^ d / Real.log D) ≤
        max 1 (Real.log (1 + t ^ d / Real.log D)) := le_max_right _ _
    have hd1 : 0 ≤ d + 1 := by linarith
    calc
      perturbationSlope D d 0 t ≤
          (d + 1) * Real.log (1 + t ^ d / Real.log D) := hs
      _ ≤ (d + 1) * max 1 (Real.log (1 + t ^ d / Real.log D)) :=
        mul_le_mul_of_nonneg_left hlogmax hd1
      _ ≤ 2 * (d + 1) * max 1 (Real.log (1 + t ^ d / Real.log D)) := by
        have hm0 : 0 ≤ max 1 (Real.log (1 + t ^ d / Real.log D)) :=
          zero_le_one.trans (le_max_left _ _)
        nlinarith
  · have hs := shifted_slope_le_log hlog hd.le ht
    have hshift := shifted_log_le_two_max hlog hd ht hdt
    have hd1 : 0 ≤ d + 1 := by linarith
    calc
      perturbationSlope D d 1 t ≤
          (d + 1) * Real.log (1 + (t + 1) ^ d / Real.log D) := hs
      _ ≤ (d + 1) *
          (2 * max 1 (Real.log (1 + t ^ d / Real.log D))) :=
        mul_le_mul_of_nonneg_left hshift hd1
      _ = 2 * (d + 1) * max 1 (Real.log (1 + t ^ d / Real.log D)) := by ring

noncomputable def derivativeHead : ℕ := ⌈max 16 sourceRatioHead⌉₊
noncomputable def derivativeCutoff : ℝ :=
  max sourceRatioCutoff (compactDerivativeCutoff derivativeHead 16)

theorem derivativeHead_sixteen : 16 ≤ derivativeHead := by
  have hh : (16 : ℝ) ≤ derivativeHead :=
    (le_max_left _ _).trans (Nat.le_ceil (max 16 sourceRatioHead))
  exact_mod_cast hh

theorem derivativeCutoff_gt_one : 1 < derivativeCutoff := by
  apply lt_of_lt_of_le _ (le_max_right _ _)
  apply Real.one_lt_exp_iff.mpr
  exact zero_lt_one.trans_le (le_max_left _ _)

/-- A fully numerical certificate for both perturbation shifts at d=16. -/
theorem numerical_derivative_certificate {H : Section13HatLayers}
    (hH : Section13HatSourceContract H) {D : ℝ} (hD : derivativeCutoff ≤ D) :
    4 ≤ sourceSigma D 16 ∧
    ∀ (sign : ErrorSign) (ε t : ℝ),
      (ε = 0 ∨ ε = 1) → 2 + sign.epsilon < t → t < sourceSigma D 16 →
        weightedHat H sign t * perturbationSlope D 16 ε t ≤
          t * H.T sign.opposite (t-1) := by
  have hratio := numerical_source_ratio hH ((le_max_left _ _).trans hD)
  have hhead4 : 4 ≤ sourceRatioHead := by
    have hh : Real.exp 2309 ≤ sourceRatioHead := le_max_left _ _
    linarith only [hh, Real.add_one_le_exp (2309 : ℝ)]
  refine ⟨hhead4.trans hratio.1, ?_⟩
  intro sign ε t hε ht htσ
  by_cases htM : t ≤ derivativeHead
  · exact numerical_compact_derivative hH.toSection13HatContract
      (show 3 ≤ derivativeHead by have hh := derivativeHead_sixteen; omega)
      (by norm_num : (0 : ℝ) ≤ 16) D ((le_max_right _ _).trans hD) sign ε t hε ht htM
  · have hMt : (derivativeHead : ℝ) ≤ t := (lt_of_not_ge htM).le
    have hMr : sourceRatioHead ≤ derivativeHead :=
      (le_max_right _ _).trans (Nat.le_ceil (max 16 sourceRatioHead))
    have h16 : (16 : ℝ) ≤ derivativeHead := by exact_mod_cast derivativeHead_sixteen
    have ht0 : 0 < t := by linarith only [h16, hMt]
    have hD1 := derivativeCutoff_gt_one.trans_le hD
    have hs := both_slopes_le_ratio_coefficient (Real.log_pos hD1)
      (by norm_num : (0 : ℝ) < 16) ht0 (h16.trans hMt) hε
    have hW0 : 0 ≤ weightedHat H sign t :=
      mul_nonneg (sq_nonneg t) (hH.positive sign t ht0).le
    calc
      _ ≤ weightedHat H sign t *
          (2*(16+1 : ℝ)*max 1 (Real.log (1+t^(16 : ℝ)/Real.log D))) :=
        mul_le_mul_of_nonneg_left hs hW0
      _ = (2*(16+1 : ℝ)*max 1 (Real.log (1+t^(16 : ℝ)/Real.log D))) *
          weightedHat H sign t := mul_comm _ _
      _ ≤ _ := hratio.2 sign t (hMr.trans hMt) htσ.le

#print axioms numerical_derivative_certificate
end ChenEffective
