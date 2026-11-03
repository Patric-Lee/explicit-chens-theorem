import NumericalForwardEnvelope
import NumericalSourceGeometry

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

noncomputable def legacySourceLowerCutoff (L : ℝ) : ℝ := Real.exp (Real.exp (max 1 L))

theorem legacy_sourceSigma_lower (d L : ℝ) (hd : 0 ≤ d) :
    ∀ D : ℝ, legacySourceLowerCutoff L ≤ D → L ≤ sourceSigma D d := by
  let X : ℝ := max 1 L
  have hX1 : 1 ≤ X := le_max_left _ _
  have hLX : L ≤ X := le_max_right _ _
  have hXpos : 0 < X := zero_lt_one.trans_le hX1
  let D₀ : ℝ := Real.exp (Real.exp X)

  change ∀ D : ℝ, D₀ ≤ D → L ≤ sourceSigma D d
  intro D hD
  have hDpos : 0 < D := (Real.exp_pos (Real.exp X)).trans_le hD
  have hlogD : Real.exp X ≤ Real.log D :=
    (Real.le_log_iff_exp_le hDpos).2 hD
  have hlogD1 : 1 ≤ Real.log D :=
    (Real.one_le_exp hXpos.le).trans hlogD
  have hpow1 : 1 ≤ (Real.log D) ^ (1 / d) := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hlogD1
        (by positivity : 0 ≤ 1 / d)
  have hlog27D : Real.log (27 * D) = Real.log 27 + Real.log D := by
    rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) (ne_of_gt hDpos)]
  have hinner : Real.exp X ≤ Real.log (27 * D) := by
    rw [hlog27D]
    have hlog27 : 0 ≤ Real.log (27 : ℝ) := (Real.log_pos (by norm_num)).le
    linarith
  have hll : X ≤ Real.log (Real.log (27 * D)) := by
    rw [← Real.log_exp X]
    exact Real.log_le_log (Real.exp_pos X) hinner
  unfold sourceSigma
  have hll0 : 0 ≤ Real.log (Real.log (27 * D)) := hXpos.le.trans hll
  calc
    L ≤ X := hLX
    _ ≤ Real.log (Real.log (27 * D)) := hll
    _ ≤ (Real.log D) ^ (1 / d) * Real.log (Real.log (27 * D)) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow1 hll0
/-- For positive d the source endpoint only needs a single exponential. The
zero-exponent compatibility branch retains the necessary double logarithm. -/
noncomputable def sourceLowerCutoffFor (d L : ℝ) : ℝ :=
  if d=0 then legacySourceLowerCutoff L
  else Real.exp (max (Real.exp 1) ((max 1 L)^d))
noncomputable def sourceLowerCutoff (L : ℝ) : ℝ := sourceLowerCutoffFor 16 L

theorem sourceLowerCutoffFor_gt_one (d L : ℝ) : 1 < sourceLowerCutoffFor d L := by
  unfold sourceLowerCutoffFor
  split
  · exact Real.one_lt_exp_iff.mpr (Real.exp_pos _)
  · exact Real.one_lt_exp_iff.mpr ((Real.exp_pos 1).trans_le (le_max_left _ _))
theorem sourceLowerCutoff_gt_one (L : ℝ) : 1 < sourceLowerCutoff L :=
  sourceLowerCutoffFor_gt_one 16 L

theorem numerical_sourceSigma_lower (d L : ℝ) (hd : 0 ≤ d) :
    ∀ D : ℝ, sourceLowerCutoffFor d L ≤ D → L ≤ sourceSigma D d := by
  by_cases hd0 : d=0
  · simpa only [sourceLowerCutoffFor,if_pos hd0] using legacy_sourceSigma_lower d L hd
  have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
  intro D hD
  have hD0 : 0 < D := (zero_lt_one.trans (sourceLowerCutoffFor_gt_one d L)).trans_le hD
  have hh : max (Real.exp 1) ((max 1 L)^d) ≤ Real.log D :=
    (Real.le_log_iff_exp_le hD0).mpr (by simpa only [sourceLowerCutoffFor,if_neg hd0] using hD)
  have he : Real.exp 1 ≤ Real.log D := (le_max_left _ _).trans hh
  have hl0 : 0 < Real.log D := (Real.exp_pos 1).trans_le he
  have hX : 0 < max (1 : ℝ) L := zero_lt_one.trans_le (le_max_left _ _)
  have hp : max 1 L ≤ (Real.log D)^(1/d) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hX.le d) ((le_max_right _ _).trans hh)
      (show 0 ≤ 1/d by positivity)
    rwa [← Real.rpow_mul hX.le,mul_one_div_cancel hd0,Real.rpow_one] at h
  have hi : Real.exp 1 ≤ Real.log (27*D) := by
    rw [Real.log_mul (by norm_num) hD0.ne']
    have h27 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 27)
    linarith only [he,h27]
  have hll : 1 ≤ Real.log (Real.log (27*D)) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hi
  exact (le_max_right (1 : ℝ) L).trans (hp.trans (by
    unfold sourceSigma
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hll (Real.rpow_nonneg hl0.le (1/d))))

noncomputable def sourceLogM (K A d : ℝ) : ℝ := Real.exp (4 * (2 * (d+1)*K^2*A) + 1)
noncomputable def sourceLogCutoff (K A d : ℝ) : ℝ :=
  let C := 2*(d+1)*K^2*A
  let e := min (d/2) (1/(4*C))
  let q := d-e
  let r := 1/q - 1/d
  let X := max 2 (max (Real.log 27) ((4/r)^(1/(r/2))))
  max (sourceLowerCutoffFor d (sourceLogM K A d)) (Real.exp X)

theorem numerical_source_log_domination {K A d : ℝ}
    (hd : 0 < d) (hK : 1 ≤ K) (hA : 1 ≤ A) :
    ∀ D : ℝ, sourceLogCutoff K A d ≤ D →
      sourceLogM K A d ≤ sourceSigma D d ∧
      ∀ t : ℝ, sourceLogM K A d ≤ t → t ≤ sourceSigma D d →
        2*(d+1)*K^2*A * max 1 (Real.log (1 + t^d / Real.log D)) ≤
          Real.log (Real.exp 1 * t) := by
  let C := 2 * (d + 1) * K ^ 2 * A
  have hC : 0 < C := by dsimp [C]; positivity
  let e := min (d / 2) (1 / (4 * C))
  have he : 0 < e := lt_min (by positivity) (by positivity)
  have hed : e < d := (min_le_left _ _).trans_lt (by linarith)
  have heC : C * e ≤ 1 / 4 := by
    calc
      C * e ≤ C * (1 / (4 * C)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le
      _ = 1 / 4 := by field_simp
  let q := d - e
  have hq : 0 < q := sub_pos.mpr hed
  let r := 1 / q - 1 / d
  have hr : 0 < r := by
    dsimp [r]
    exact sub_pos.mpr (one_div_lt_one_div_of_lt hq (by dsimp [q]; linarith))
  let X := max 2 (max (Real.log 27) ((4 / r) ^ (1 / (r / 2))))
  let M := Real.exp (4 * C + 1)
  have hM : 1 < M := Real.one_lt_exp_iff.mpr (by positivity)
  let D₁ := sourceLowerCutoffFor d M
  have hlower := numerical_sourceSigma_lower d M hd.le
  change ∀ D : ℝ, max D₁ (Real.exp X) ≤ D → _
  intro D hD
  refine ⟨hlower D ((le_max_left _ _).trans hD), ?_⟩
  have hDX : Real.exp X ≤ D := (le_max_right _ _).trans hD
  have hDpos : 0 < D := (Real.exp_pos X).trans_le hDX
  have hX : X ≤ Real.log D := (Real.le_log_iff_exp_le hDpos).mpr hDX
  let x := Real.log D
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hX
  have hx : 0 < x := by linarith
  have hx27 : Real.log 27 ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hX)
  have hxroot : (4 / r) ^ (1 / (r / 2)) ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hX)
  have hxpow : 4 / r ≤ x ^ (r / 2) := by
    apply (Real.rpow_inv_le_iff_of_pos (by positivity) hx.le (by positivity)).mp
    simpa only [one_div] using hxroot
  -- A positive power absorbs the iterated logarithm at the actual source cutoff.
  have hlog : 2 * Real.log x ≤ x ^ r := by
    calc
      2 * Real.log x ≤ 2 * (x ^ (r / 2) / (r / 2)) :=
        mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hx.le (by positivity)) (by norm_num)
      _ = (4 / r) * x ^ (r / 2) := by ring
      _ ≤ x ^ (r / 2) * x ^ (r / 2) :=
        mul_le_mul_of_nonneg_right hxpow (Real.rpow_nonneg hx.le _)
      _ = x ^ r := by rw [← Real.rpow_add hx]; congr 1; ring
  have hinner : Real.log (27 * D) = Real.log 27 + x :=
    Real.log_mul (by norm_num) hDpos.ne'
  have hinnerpos : 0 < Real.log (27 * D) := by
    rw [hinner]
    exact add_pos (Real.log_pos (by norm_num)) hx
  have hll : Real.log (Real.log (27 * D)) ≤ x ^ r := by
    calc
      Real.log (Real.log (27 * D)) ≤ Real.log (2 * x) :=
        Real.log_le_log hinnerpos (by rw [hinner]; linarith)
      _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hx.ne'
      _ ≤ 2 * Real.log x := by
        have := Real.log_le_log (by norm_num : (0:ℝ) < 2) hx2
        linarith
      _ ≤ x ^ r := hlog
  have hsigma : sourceSigma D d ≤ x ^ (1 / q) := by
    calc
      sourceSigma D d ≤ x ^ (1 / d) * x ^ r := by
        simpa only [sourceSigma] using
          mul_le_mul_of_nonneg_left hll (Real.rpow_nonneg hx.le _)
      _ = x ^ (1 / q) := by
        rw [← Real.rpow_add hx]
        congr 1
        dsimp [r]
        ring
  intro t ht hts
  have ht1 : 1 < t := hM.trans_le ht
  have ht0 : 0 < t := zero_lt_one.trans ht1
  have hlt : 4 * C + 1 ≤ Real.log t := (Real.le_log_iff_exp_le ht0).mpr ht
  have hlogt : 0 ≤ Real.log t := (Real.log_pos ht1).le
  have htpow : t ^ q ≤ x := by
    have := Real.rpow_le_rpow ht0.le (hts.trans hsigma) hq.le
    simpa only [← Real.rpow_mul hx.le, one_div_mul_cancel hq.ne', Real.rpow_one] using this
  have hratio : t ^ d / Real.log D ≤ t ^ e := by
    apply (div_le_iff₀ hx).mpr
    calc
      t ^ d = t ^ e * t ^ q := by
        rw [← Real.rpow_add ht0]
        congr 1
        dsimp [q]
        ring
      _ ≤ t ^ e * x := mul_le_mul_of_nonneg_left htpow (Real.rpow_nonneg ht0.le _)
  have hte : 1 ≤ t ^ e := Real.one_le_rpow ht1.le he.le
  have hlogratio : Real.log (1 + t ^ d / Real.log D) ≤ Real.log 2 + e * Real.log t := by
    calc
      Real.log (1 + t ^ d / Real.log D) ≤ Real.log (2 * t ^ e) :=
        Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + e * Real.log t := by
        rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos ht0 e).ne', Real.log_rpow ht0]
  have hC1 : C ≤ Real.log t := by linarith only [hlt, hC]
  have hClog : C * Real.log (1 + t ^ d / Real.log D) ≤ Real.log t := by
    have hce := mul_le_mul_of_nonneg_right heC hlogt
    have hcb := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)) hC.le
    have hmain := mul_le_mul_of_nonneg_left hlogratio hC.le
    linarith only [hce, hcb, hmain, hlt, hlogt]
  change C * max 1 (Real.log (1 + t ^ d / Real.log D)) ≤ _
  rw [mul_max_of_nonneg _ _ hC.le, mul_one]
  have hmax := max_le hC1 hClog
  rw [Real.log_mul (Real.exp_ne_zero 1) ht0.ne', Real.log_exp]
  exact hmax.trans (le_add_of_nonneg_left zero_le_one)

#print axioms numerical_source_log_domination
end ChenEffective
