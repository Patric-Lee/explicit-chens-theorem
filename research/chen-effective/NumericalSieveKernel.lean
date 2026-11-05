import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
Analytic bounds for the elementary specialized-sieve hat. The exponential
integral is bounded by a rational differential supersolution, rather than a
numerical quadrature table.
-/

namespace ChenEffective
open Real Set Filter MeasureTheory intervalIntegral
open scoped Topology
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

noncomputable def sieveHat (s : ℝ) : ℝ :=
  if s ≤ 2 then exp (-2) else if s ≤ 3 then exp (-s) else 3 * exp (-s) / s

noncomputable def sieveExpIntegral (a : ℝ) : ℝ :=
  ∫ t in Ioi a, exp (-t) / t

noncomputable def sieveTailRational (a : ℝ) : ℝ := (a + 1) / (a * (a + 2))

theorem sieve_exp_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => exp (-t) / t) (Ioi a) := by
  apply Integrable.mono' ((integrableOn_exp_neg_Ioi a).const_mul (1 / a))
  · exact (Real.measurable_exp.comp measurable_neg |>.div measurable_id).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ha.trans ht
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (exp_pos _) ht0)]
    simpa [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le ha ht.le) (exp_pos (-t)).le

private theorem sieveTailRational_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ sieveTailRational t := by unfold sieveTailRational; positivity

private theorem sieveTailRational_le_one {t : ℝ} (ht : 1 ≤ t) :
    sieveTailRational t ≤ 1 := by
  unfold sieveTailRational
  apply (div_le_one (by positivity)).mpr
  nlinarith

private theorem sieveTailRational_limit :
    Tendsto (fun t : ℝ => -(exp (-t) * sieveTailRational t)) atTop (𝓝 0) := by
  have hp : Tendsto (fun t : ℝ => exp (-t) * sieveTailRational t) atTop (𝓝 0) := by
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      exact mul_nonneg (exp_pos _).le (sieveTailRational_nonneg (by linarith))
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      simpa using mul_le_mul_of_nonneg_left (sieveTailRational_le_one ht) (exp_pos (-t)).le
    · exact tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  simpa using hp.neg

private theorem sieveTailRational_deriv {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => -(exp (-x) * sieveTailRational x))
      (exp (-t) * (1 / t + 2 / (t ^ 2 * (t + 2) ^ 2))) t := by
  have htne : t ≠ 0 := ht.ne'
  have ht2 : t + 2 ≠ 0 := by linarith
  have hr := ((hasDerivAt_id t).add_const 1).div
    ((hasDerivAt_id t).mul ((hasDerivAt_id t).add_const 2)) (mul_ne_zero htne ht2)
  have hh := (((hasDerivAt_id t).neg.exp).mul hr).neg
  apply hh.congr_deriv
  dsimp
  field_simp [htne, ht2]
  ring

theorem sieveExpIntegral_rational_bound {a : ℝ} (ha : 0 < a) :
    sieveExpIntegral a ≤ exp (-a) * sieveTailRational a := by
  let f := fun t : ℝ => exp (-t) * (1 / t + 2 / (t ^ 2 * (t + 2) ^ 2))
  have hd : ∀ t ∈ Ici a, HasDerivAt
      (fun x : ℝ => -(exp (-x) * sieveTailRational x)) (f t) t :=
    fun t ht => sieveTailRational_deriv (ha.trans_le ht)
  have hn : ∀ t ∈ Ioi a, 0 ≤ f t := by
    intro t ht
    dsimp [f]
    have ht0 : 0 < t := ha.trans ht
    positivity
  have hi := integrableOn_Ioi_deriv_of_nonneg' hd hn sieveTailRational_limit
  have he := integral_Ioi_of_hasDerivAt_of_nonneg' hd hn sieveTailRational_limit
  unfold sieveExpIntegral
  calc
    _ ≤ ∫ t in Ioi a, f t := by
      apply setIntegral_mono_on (sieve_exp_integrable ha) hi measurableSet_Ioi
      intro t ht
      dsimp [f]
      have ht0 : 0 < t := ha.trans ht
      rw [div_eq_mul_inv, one_div]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (exp_pos _).le
    _ = _ := by simpa using he

theorem sieveExpIntegral_three : sieveExpIntegral 3 ≤ (4 / 15 : ℝ) * exp (-3) := by
  have h := sieveExpIntegral_rational_bound (by norm_num : (0 : ℝ) < 3)
  norm_num [sieveTailRational] at h
  nlinarith only [h]

theorem sieveHat_pos (s : ℝ) : 0 < sieveHat s := by
  unfold sieveHat
  split_ifs with h2 h3
  · positivity
  · positivity
  · have : 0 < s := by linarith
    positivity

theorem sieveHat_le_exp (s : ℝ) : sieveHat s ≤ exp (-s) := by
  unfold sieveHat
  split_ifs with h2 h3
  · exact exp_le_exp.mpr (by linarith)
  · exact le_rfl
  · have hs : 0 < s := by linarith
    exact (div_le_iff₀ hs).mpr (by nlinarith [exp_pos (-s)])

theorem sieveHat_measurable : Measurable sieveHat := by
  unfold sieveHat
  exact Measurable.ite measurableSet_Iic measurable_const
    (Measurable.ite measurableSet_Iic (Real.measurable_exp.comp measurable_neg)
      ((measurable_const.mul (Real.measurable_exp.comp measurable_neg)).div measurable_id))

theorem sieveHat_integrable (a : ℝ) : IntegrableOn sieveHat (Ioi a) := by
  apply Integrable.mono' (integrableOn_exp_neg_Ioi a) sieveHat_measurable.aestronglyMeasurable
  filter_upwards with t
  simpa only [Real.norm_eq_abs, abs_of_pos (sieveHat_pos t)] using sieveHat_le_exp t

noncomputable def sieveHatTail (s : ℝ) : ℝ := ∫ t in Ioi (s - 1), sieveHat t

theorem sieveHatTail_ge_four {s : ℝ} (hs : 4 ≤ s) :
    sieveHatTail s = 3 * sieveExpIntegral (s - 1) := by
  unfold sieveHatTail sieveExpIntegral
  rw [← MeasureTheory.integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht3 : ¬t ≤ 3 := by have := ht; simp only [mem_Ioi] at this; linarith
  simp only [sieveHat, if_neg (by linarith : ¬t ≤ 2), if_neg ht3]
  ring

private theorem sieveHat_tail_three :
    (∫ t in Ioi (3 : ℝ), sieveHat t) = 3 * sieveExpIntegral 3 := by
  have h := sieveHatTail_ge_four (by norm_num : (4 : ℝ) ≤ 4)
  simpa only [sieveHatTail, show (4 : ℝ) - 1 = 3 by norm_num] using h

private theorem integral_exp_neg_interval (a b : ℝ) :
    (∫ t in a..b, exp (-t)) = exp (-a) - exp (-b) := by
  rw [intervalIntegral.integral_comp_neg, integral_exp]

theorem sieveHatTail_middle {s : ℝ} (hs : 3 ≤ s) (hs4 : s ≤ 4) :
    sieveHatTail s = exp (1 - s) - exp (-3) + 3 * sieveExpIntegral 3 := by
  have ha : 2 ≤ s - 1 := by linarith
  have hab : s - 1 ≤ 3 := by linarith
  have hi : (∫ t in (s - 1)..3, sieveHat t) =
      (∫ t in (s - 1)..3, exp (-t)) := by
    apply integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht2 : 2 ≤ t := ha.trans ht.1
    by_cases h2 : t ≤ 2
    · have : t = 2 := by linarith
      norm_num [this, sieveHat]
    · simp [sieveHat, h2, ht.2]
  have hsplit := integral_interval_add_Ioi (sieveHat_integrable (s - 1)) (sieveHat_integrable 3)
  rw [hi, integral_exp_neg_interval, sieveHat_tail_three] at hsplit
  unfold sieveHatTail
  simpa only [show -(s - 1) = 1 - s by ring] using hsplit.symm

theorem sieveHatTail_low {s : ℝ} (_hs : 2 ≤ s) (hs3 : s ≤ 3) :
    sieveHatTail s = (4 - s) * exp (-2) - exp (-3) + 3 * sieveExpIntegral 3 := by
  have hab : s - 1 ≤ 2 := by linarith
  have hi : (∫ t in (s - 1)..2, sieveHat t) = (3 - s) * exp (-2) := by
    have he : (∫ t in (s - 1)..2, sieveHat t) =
        ∫ _t in (s - 1)..2, exp (-2) := by
      apply integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      simp [sieveHat, ht.2]
    rw [he, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  have hsplit := integral_interval_add_Ioi (sieveHat_integrable (s - 1)) (sieveHat_integrable 2)
  have hthree := sieveHatTail_middle (by norm_num : (3 : ℝ) ≤ 3) (by norm_num : (3 : ℝ) ≤ 4)
  norm_num only [sieveHatTail, show (3 : ℝ) - 1 = 2 by norm_num] at hthree
  rw [hi, hthree] at hsplit
  unfold sieveHatTail
  rw [← hsplit]
  ring

private theorem exp_one_le_25_div_9 : exp 1 ≤ (25 / 9 : ℝ) := by
  linarith [Real.exp_one_lt_d9]

private theorem exp_neg_one_ge : (9 / 25 : ℝ) ≤ exp (-1) := by
  rw [exp_neg, inv_eq_one_div]
  apply (le_div_iff₀ (exp_pos 1)).mpr
  nlinarith only [exp_one_le_25_div_9]

private noncomputable def lowKernelModel (c r : ℝ) : ℝ :=
  exp r * (2 - r - c) / (r + 2)

private theorem lowKernelModel_deriv {c r : ℝ} (hr : 0 ≤ r) :
    HasDerivAt (lowKernelModel c)
      (exp r * (-(r ^ 2) - c * r - c) / (r + 2) ^ 2) r := by
  have hh := ((hasDerivAt_exp r).mul ((hasDerivAt_const r (2 : ℝ)).sub
    (hasDerivAt_id r) |>.sub_const c)).div ((hasDerivAt_id r).add_const 2)
      (by linarith : r + 2 ≠ 0)
  apply hh.congr_deriv
  dsimp
  field_simp
  ring

private theorem lowKernelModel_antitone {c : ℝ} (hc : 0 ≤ c) :
    AntitoneOn (lowKernelModel c) (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · intro r hr
    exact (lowKernelModel_deriv hr).continuousAt.continuousWithinAt
  · intro r hr
    exact (lowKernelModel_deriv (interior_subset hr)).differentiableAt.differentiableWithinAt
  · intro r hr
    have hr0 : 0 ≤ r := interior_subset hr
    rw [(lowKernelModel_deriv hr0).deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    apply mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le
    nlinarith only [sq_nonneg r, mul_nonneg hc hr0, hr0, hc]

theorem sieveHatTail_contraction_low {s : ℝ} (hs : 2 ≤ s) (hs3 : s ≤ 3) :
    sieveHatTail s ≤ (241 / 250 : ℝ) * s * sieveHat s := by
  let c := exp (-1) / 5
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hm := lowKernelModel_antitone hc (show (0 : ℝ) ∈ Ici 0 by simp)
    (show s - 2 ∈ Ici 0 by simp only [mem_Ici]; linarith) (by linarith : 0 ≤ s - 2)
  have hm0 : lowKernelModel c 0 ≤ (241 / 250 : ℝ) := by
    dsimp [lowKernelModel, c]
    rw [exp_zero]
    linarith only [exp_neg_one_ge]
  have hupper : sieveHatTail s ≤ (4 - s) * exp (-2) - exp (-3) / 5 := by
    rw [sieveHatTail_low hs hs3]
    nlinarith only [sieveExpIntegral_three]
  have he3 : exp (-3 : ℝ) = exp (-2) * exp (-1) := by rw [← exp_add]; norm_num
  have hec : exp (-s) * exp (s - 2) = exp (-2) := by
    rw [← exp_add]; congr 1; ring
  have hid : (4 - s) * exp (-2) - exp (-3) / 5 =
      exp (-s) * s * lowKernelModel c (s - 2) := by
    unfold lowKernelModel
    dsimp only [c]
    rw [he3, ← hec, show s - 2 + 2 = s by ring]
    have hs0 : s ≠ 0 := by linarith
    field_simp [hs0]
    ring
  have hh : sieveHat s = exp (-s) := by
    by_cases h2 : s ≤ 2
    · have : s = 2 := by linarith
      simp [sieveHat, this]
    · simp [sieveHat, h2, hs3]
  rw [hid] at hupper
  rw [hh]
  have hmodel := hm.trans hm0
  have hmul := mul_le_mul_of_nonneg_left hmodel
    (show 0 ≤ exp (-s) * s by positivity)
  nlinarith only [hupper, hmul]

theorem sieveHatTail_le_exp (s : ℝ) : sieveHatTail s ≤ exp (1 - s) := by
  unfold sieveHatTail
  calc
    _ ≤ ∫ t in Ioi (s - 1), exp (-t) := by
      apply setIntegral_mono_on (sieveHat_integrable _) (integrableOn_exp_neg_Ioi _) measurableSet_Ioi
      intro t _; exact sieveHat_le_exp t
    _ = _ := by rw [integral_exp_neg_Ioi]; congr 1; ring

theorem sieveHatTail_contraction_high {s : ℝ} (hs : 3 ≤ s) :
    sieveHatTail s ≤ (25 / 27 : ℝ) * s * sieveHat s := by
  have hh : s * sieveHat s = 3 * exp (-s) := by
    by_cases h3 : s ≤ 3
    · have : s = 3 := by linarith
      norm_num [this, sieveHat]
    · simp only [sieveHat, if_neg (by linarith : ¬s ≤ 2), if_neg h3]
      field_simp
  have he : exp (1 - s) = exp 1 * exp (-s) := by
    simpa only [sub_eq_add_neg] using exp_add (1 : ℝ) (-s)
  have hmul := mul_le_mul_of_nonneg_right exp_one_le_25_div_9 (exp_pos (-s)).le
  have ht := sieveHatTail_le_exp s
  rw [he] at ht
  nlinarith only [hh, hmul, ht]

theorem sieveHatTail_contraction {s : ℝ} (hs : 2 ≤ s) :
    sieveHatTail s ≤ (241 / 250 : ℝ) * s * sieveHat s := by
  by_cases hs3 : s ≤ 3
  · exact sieveHatTail_contraction_low hs hs3
  · have h := sieveHatTail_contraction_high (le_of_not_ge hs3)
    have hp := sieveHat_pos s
    nlinarith only [h, mul_pos (by linarith : 0 < s) hp]

private theorem weighted_exp_antitone :
    AntitoneOn (fun s : ℝ => s * exp (-s)) (Ici 1) := by
  have hd (s : ℝ) : HasDerivAt (fun t : ℝ => t * exp (-t))
      ((1 - s) * exp (-s)) s := by
    have hh := (hasDerivAt_id s).mul (hasDerivAt_id s).neg.exp
    apply hh.congr_deriv
    dsimp
    ring
  apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
  · intro s _; exact (hd s).continuousAt.continuousWithinAt
  · intro s _; exact (hd s).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [(hd s).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (by have := interior_subset hs; simp_all) (exp_pos _).le

theorem sieveHat_weighted_compact {s : ℝ} (hs : 1 ≤ s) (hs3 : s ≤ 3) :
    exp (-2) ≤ s * sieveHat s := by
  by_cases hs2 : s ≤ 2
  · simp only [sieveHat, if_pos hs2]
    nlinarith only [hs, exp_pos (-2)]
  · have hm := weighted_exp_antitone (show s ∈ Ici 1 from hs)
      (show (3 : ℝ) ∈ Ici 1 by norm_num) hs3
    have he : exp (-2 : ℝ) = exp 1 * exp (-3) := by rw [← exp_add]; norm_num
    have hb := mul_le_mul_of_nonneg_right (show exp 1 ≤ (3 : ℝ) from Real.exp_one_lt_three.le)
      (exp_pos (-3)).le
    simp only [sieveHat, if_neg hs2, if_pos hs3]
    rw [he]
    exact hb.trans hm

theorem sieveHatTail_compact {s : ℝ} (hs : 1 ≤ s) (hs3 : s ≤ 3) :
    sieveHatTail 3 ≤ (116 / 125 : ℝ) * s * sieveHat s := by
  have ht : sieveHatTail 3 ≤ exp (-2) - exp (-3) / 5 := by
    rw [sieveHatTail_middle (by norm_num) (by norm_num)]
    norm_num only
    nlinarith only [sieveExpIntegral_three]
  have he3 : exp (-3 : ℝ) = exp (-2) * exp (-1) := by rw [← exp_add]; norm_num
  have hc := sieveHat_weighted_compact hs hs3
  have hb := mul_le_mul_of_nonneg_left exp_neg_one_ge (exp_pos (-2)).le
  rw [he3] at ht
  nlinarith only [ht, hb, hc]

theorem sieveHatTail_parity {s : ℝ} (hs : 1 ≤ s) :
    sieveHatTail (max s 3) ≤ (241 / 250 : ℝ) * s * sieveHat s := by
  by_cases hs3 : s ≤ 3
  · rw [max_eq_right hs3]
    have h := sieveHatTail_compact hs hs3
    nlinarith only [h, mul_pos (by linarith : 0 < s) (sieveHat_pos s)]
  · rw [max_eq_left (le_of_not_ge hs3)]
    exact sieveHatTail_contraction (by linarith)

theorem sieveHat_max_formula (s : ℝ) :
    sieveHat s = exp (-max 2 s) * (3 / max 3 s) := by
  by_cases hs2 : s ≤ 2
  · have hs3 : s ≤ 3 := by linarith
    norm_num [sieveHat, hs2, max_eq_left hs2, max_eq_left hs3]
  · by_cases hs3 : s ≤ 3
    · norm_num [sieveHat, hs2, hs3, max_eq_right (le_of_not_ge hs2), max_eq_left hs3]
    · simp only [sieveHat, if_neg hs2, if_neg hs3, max_eq_right (le_of_not_ge hs2),
        max_eq_right (le_of_not_ge hs3)]
      ring

theorem sieveHat_continuous : Continuous sieveHat := by
  have he : sieveHat = fun s : ℝ => exp (-max 2 s) * (3 / max 3 s) :=
    funext sieveHat_max_formula
  rw [he]
  apply Continuous.mul
  · fun_prop
  · apply Continuous.div continuous_const (continuous_const.max continuous_id)
    intro s
    change max (3 : ℝ) s ≠ 0
    have hh : (3 : ℝ) ≤ max 3 s := le_max_left _ _
    linarith

theorem sieveHat_antitone : Antitone sieveHat := by
  intro x y hxy
  rw [sieveHat_max_formula x, sieveHat_max_formula y]
  apply mul_le_mul
  · exact exp_le_exp.mpr (neg_le_neg (max_le_max_left 2 hxy))
  · exact div_le_div_of_nonneg_left (by norm_num)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) (le_max_left _ _))
      (max_le_max_left 3 hxy)
  · positivity
  · positivity

theorem sieveHat_shift (s : ℝ) : sieveHat (s - 1) ≤ 4 * sieveHat s := by
  have h2 : max 2 s ≤ max 2 (s - 1) + 1 := by
    apply max_le
    · have := le_max_left (2 : ℝ) (s - 1); linarith
    · have := le_max_right (2 : ℝ) (s - 1); linarith
  have h3 : max 3 s ≤ (4 / 3 : ℝ) * max 3 (s - 1) := by
    have hlo := le_max_left (3 : ℝ) (s - 1)
    have hh : max 3 s ≤ max 3 (s - 1) + 1 := by
      apply max_le
      · linarith
      · have := le_max_right (3 : ℝ) (s - 1); linarith
    linarith
  have hE : exp (-max 2 (s - 1)) ≤ exp 1 * exp (-max 2 s) := by
    rw [← exp_add]
    exact exp_le_exp.mpr (by linarith only [h2])
  have hR : 3 / max 3 (s - 1) ≤ (4 / 3 : ℝ) * (3 / max 3 s) := by
    have hp : 0 < max 3 (s - 1) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hq : 0 < max 3 s := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    rw [show (4 / 3 : ℝ) * (3 / max 3 s) = 4 / max 3 s by ring]
    exact (div_le_div_iff₀ hp hq).mpr (by nlinarith only [h3])
  rw [sieveHat_max_formula (s - 1), sieveHat_max_formula s]
  have hh := mul_le_mul hE hR (by positivity) (by positivity)
  have he := mul_le_mul_of_nonneg_right (show exp 1 ≤ (3 : ℝ) from exp_one_lt_three.le)
    (show 0 ≤ exp (-max 2 s) * (3 / max 3 s) by positivity)
  nlinarith only [hh, he]

#print axioms sieveHatTail_contraction
#print axioms sieveHatTail_compact

#print axioms sieveExpIntegral_rational_bound
end ChenEffective
