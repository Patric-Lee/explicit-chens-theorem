import MathlibNt.AnalyticNumberTheory.LargeSieve.DirichLTwistedNonquadraticPointwiseSiegelWalfisz

/-! A C1 polynomial smoothing kernel with rational normalization and a
numerical derivative bound. It avoids the unspecified derivative maximum of
the general smooth bump used in the original analytic route. -/
namespace ChenEffective
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology

noncomputable def positiveSquare (x : ℝ) : ℝ := (max x 0) ^ 2

theorem positiveSquare_hasDerivAt (x : ℝ) :
    HasDerivAt positiveSquare (2 * max x 0) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have heq : positiveSquare =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
      change y < 0 at hy
      simp only [positiveSquare, max_eq_right hy.le, zero_pow (by decide : 2 ≠ 0)]
    simpa [max_eq_right hx.le] using (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq
  · have hl : HasDerivWithinAt positiveSquare 0 (Iic 0) 0 := by
      apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr
      · intro y hy
        change y ≤ 0 at hy
        simp only [positiveSquare, max_eq_right hy, zero_pow (by decide : 2 ≠ 0)]
      · simp [positiveSquare]
    have hr : HasDerivWithinAt positiveSquare 0 (Ici 0) 0 := by
      have hp : HasDerivAt (fun y : ℝ => y ^ 2) 0 0 := by
        convert! hasDerivAt_pow 2 (0 : ℝ) using 1
        norm_num
      apply hp.hasDerivWithinAt.congr
      · intro y hy
        change 0 ≤ y at hy
        simp only [positiveSquare, max_eq_left hy]
      · simp [positiveSquare]
    have hu := hl.union hr
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at hu
    simpa using hu
  · have heq : positiveSquare =ᶠ[𝓝 x] (fun y : ℝ => y ^ 2) := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      change 0 < y at hy
      simp only [positiveSquare, max_eq_left hy.le]
    simpa [max_eq_left hx.le] using ((hasDerivAt_id x).pow 2).congr_of_eventuallyEq heq

theorem positiveSquare_contDiff : ContDiff ℝ 1 positiveSquare := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (positiveSquare_hasDerivAt x).differentiableAt, ?_⟩
  have heq : deriv positiveSquare = fun x => 2 * max x 0 := by
    funext x
    exact (positiveSquare_hasDerivAt x).deriv
  rw [heq]
  fun_prop

noncomputable def numericalSmoothing (x : ℝ) : ℝ :=
  (320 / 81 : ℝ) * x * positiveSquare (x - 1 / 2) * positiveSquare (2 - x)

theorem numericalSmoothing_contDiff : ContDiff ℝ 1 numericalSmoothing := by
  unfold numericalSmoothing
  exact ((contDiff_const.mul contDiff_id).mul
    (positiveSquare_contDiff.comp (contDiff_id.sub contDiff_const))).mul
      (positiveSquare_contDiff.comp (contDiff_const.sub contDiff_id))

theorem numericalSmoothing_nonneg (x : ℝ) : 0 ≤ numericalSmoothing x := by
  by_cases hx : 0 ≤ x
  · unfold numericalSmoothing positiveSquare
    positivity
  · have h : x - 1 / 2 ≤ 0 := by linarith
    simp only [numericalSmoothing, positiveSquare, max_eq_right h, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, le_refl]

theorem numericalSmoothing_support : Function.support numericalSmoothing ⊆ Icc (1 / 2) 2 := by
  intro x hx
  by_contra h
  have hz : numericalSmoothing x = 0 := by
    rcases not_and_or.mp h with h | h
    · have ht : x - 1 / 2 ≤ 0 := by linarith only [not_le.mp h]
      simp only [numericalSmoothing, positiveSquare, max_eq_right ht, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul]
    · have ht : 2 - x ≤ 0 := by linarith only [not_le.mp h]
      simp only [numericalSmoothing, positiveSquare, max_eq_right ht, zero_pow (by decide : 2 ≠ 0), mul_zero]
  exact hx hz

noncomputable def numericalSmoothingDerivative (x : ℝ) : ℝ :=
  (320 / 81 : ℝ) * positiveSquare (x - 1 / 2) * positiveSquare (2 - x) +
  (320 / 81 : ℝ) * x * (2 * max (x - 1 / 2) 0) * positiveSquare (2 - x) -
  (320 / 81 : ℝ) * x * positiveSquare (x - 1 / 2) * (2 * max (2 - x) 0)

theorem numericalSmoothing_hasDerivAt (x : ℝ) :
    HasDerivAt numericalSmoothing (numericalSmoothingDerivative x) x := by
  have hc := (hasDerivAt_const x (320 / 81 : ℝ)).mul (hasDerivAt_id x)
  have ha := (positiveSquare_hasDerivAt (x - 1 / 2)).comp x
    ((hasDerivAt_id x).sub_const (1 / 2))
  have hb := (positiveSquare_hasDerivAt (2 - x)).comp x
    ((hasDerivAt_const x (2 : ℝ)).sub (hasDerivAt_id x))
  convert! (hc.mul ha).mul hb using 1
  dsimp only [numericalSmoothingDerivative, Pi.mul_apply, Function.comp_apply, id_eq]
  ring

theorem numericalSmoothing_deriv_bound {x : ℝ} (hx : x ∈ Icc (1 / 2) 2) :
    ‖deriv numericalSmoothing x‖ ≤ 128 := by
  have ha : 0 ≤ x - 1 / 2 := by linarith only [hx.1]
  have hb : 0 ≤ 2 - x := by linarith only [hx.2]
  have ha' : x - 1 / 2 ≤ 3 / 2 := by linarith only [hx.2]
  have hb' : 2 - x ≤ 3 / 2 := by linarith only [hx.1]
  have hx0 : 0 ≤ x := by linarith only [hx.1]
  rw [(numericalSmoothing_hasDerivAt x).deriv, Real.norm_eq_abs]
  simp only [numericalSmoothingDerivative, positiveSquare, max_eq_left ha, max_eq_left hb]
  let P : ℝ := (320 / 81 : ℝ) * (x - 1 / 2) ^ 2 * (2 - x) ^ 2
  let Q : ℝ := (320 / 81 : ℝ) * x * (2 * (x - 1 / 2)) * (2 - x) ^ 2
  let R : ℝ := (320 / 81 : ℝ) * x * (x - 1 / 2) ^ 2 * (2 * (2 - x))
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hP : P ≤ 20 := by
    calc
      P ≤ (320 / 81 : ℝ) * (3 / 2) ^ 2 * (3 / 2) ^ 2 := by dsimp [P]; gcongr
      _ ≤ 20 := by norm_num
  have hQ : Q ≤ 54 := by
    calc
      Q ≤ (320 / 81 : ℝ) * 2 * (2 * (3 / 2)) * (3 / 2) ^ 2 := by
        dsimp [Q]
        gcongr
        exact hx.2
      _ ≤ 54 := by norm_num
  have hR : R ≤ 54 := by
    calc
      R ≤ (320 / 81 : ℝ) * 2 * (3 / 2) ^ 2 * (2 * (3 / 2)) := by
        dsimp [R]
        gcongr
        exact hx.2
      _ ≤ 54 := by norm_num
  change |P + Q - R| ≤ 128
  calc
    _ ≤ |P + Q| + |R| := abs_sub _ _
    _ ≤ |P| + |Q| + |R| := add_le_add (abs_add_le P Q) le_rfl
    _ = P + Q + R := by rw [abs_of_nonneg hP0, abs_of_nonneg hQ0, abs_of_nonneg hR0]
    _ ≤ 128 := by linarith only [hP, hQ, hR]

theorem numericalSmoothing_mass_one :
    ∫ x in Ioi (0 : ℝ), numericalSmoothing x / x = 1 := by
  have hsupp : Function.support (fun x => numericalSmoothing x / x) ⊆ Icc (1 / 2) 2 := by
    rw [Function.support_div]
    exact inter_subset_left.trans numericalSmoothing_support
  rw [SetIntegral.integral_eq_integral_inter_of_support_subset_Icc hsupp
    (by intro x hx; exact lt_of_lt_of_le (by norm_num) hx.1)]
  have heq : ∀ x ∈ Icc (1 / 2 : ℝ) 2,
      numericalSmoothing x / x = (320 / 81 : ℝ) * (x - 1 / 2) ^ 2 * (2 - x) ^ 2 := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hx.1)
    unfold numericalSmoothing positiveSquare
    rw [max_eq_left (by linarith only [hx.1]), max_eq_left (by linarith only [hx.2])]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Icc heq]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)]
  let F : ℝ → ℝ := fun x => (320 / 81 : ℝ) *
    (x ^ 5 / 5 - 5 * x ^ 4 / 4 + 11 * x ^ 3 / 4 - 5 * x ^ 2 / 2 + x)
  have hd : ∀ x : ℝ, HasDerivAt F
      ((320 / 81 : ℝ) * (x - 1 / 2) ^ 2 * (2 - x) ^ 2) x := by
    intro x
    convert! (hasDerivAt_const x (320 / 81 : ℝ)).mul
      ((((((hasDerivAt_pow 5 x).div_const 5).sub
        (((hasDerivAt_const x (5 : ℝ)).mul (hasDerivAt_pow 4 x)).div_const 4)).add
        (((hasDerivAt_const x (11 : ℝ)).mul (hasDerivAt_pow 3 x)).div_const 4)).sub
        (((hasDerivAt_const x (5 : ℝ)).mul (hasDerivAt_pow 2 x)).div_const 2)).add
        (hasDerivAt_id x)) using 1
    ring
  have hint : IntervalIntegrable
      (fun x : ℝ => (320 / 81 : ℝ) * (x - 1 / 2) ^ 2 * (2 - x) ^ 2)
      volume (1 / 2) 2 := Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hint]
  norm_num [F]

#print axioms numericalSmoothing_contDiff
#print axioms numericalSmoothing_deriv_bound
#print axioms numericalSmoothing_mass_one
end ChenEffective
