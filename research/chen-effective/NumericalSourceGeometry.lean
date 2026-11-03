import NumericalCaseBCutoff
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSourceRoundedGeometryPacket
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144RecursiveCoordinateSourceSigma

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LinearSieve MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144Equation1410
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable def sourceSigmaTwoCutoff (d : ℝ) : ℝ :=
  let a := (1-1/d)/2
  let C := max 1 (2 * Real.log 2 / a)
  Real.exp (max 2 (max (Real.log 27) (C^(1/a))))

theorem numerical_sourceSigma_three (d : ℝ) (hd : 0 < d) :
    ∀ D : ℝ, Real.exp (Real.exp 3) ≤ D → 3 ≤ sourceSigma D d := by
  let D0 : ℝ := Real.exp (Real.exp 3)

  change ∀ D : ℝ, D0 ≤ D → 3 ≤ sourceSigma D d
  intro D hD
  have hDpos : 0 < D := (Real.exp_pos (Real.exp 3)).trans_le hD
  have hx : Real.exp 3 ≤ Real.log D :=
    (Real.le_log_iff_exp_le hDpos).2 hD
  have hxone : 1 ≤ Real.log D := by
    have : 1 ≤ Real.exp 3 := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 3))
    linarith
  have hpow : 1 ≤ (Real.log D) ^ (1 / d) := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hxone
        (by positivity : 0 ≤ 1 / d)
  have hlog27D : Real.log (27 * D) = Real.log 27 + Real.log D := by
    rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) (ne_of_gt hDpos)]
  have hinner : Real.exp 3 ≤ Real.log (27 * D) := by
    rw [hlog27D]
    have hlog27 : 0 ≤ Real.log (27 : ℝ) := (Real.log_pos (by norm_num)).le
    linarith
  have hll : 3 ≤ Real.log (Real.log (27 * D)) := by
    rw [← Real.log_exp 3]
    exact Real.log_le_log (Real.exp_pos 3) hinner
  unfold sourceSigma
  nlinarith [mul_nonneg (sub_nonneg.mpr hpow) (sub_nonneg.mpr hll)]

theorem numerical_sourceSigma_two (d : ℝ) (hd : 1 < d) :
    ∀ D : ℝ, sourceSigmaTwoCutoff d ≤ D → 2 ≤ D^(1 / sourceSigma D d) := by
  let a : ℝ := (1 - 1 / d) / 2
  have hd0 : 0 < d := zero_lt_one.trans hd
  have ha : 0 < a := by
    dsimp [a]
    have hrecip := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hd
    have : 1 / d < 1 := by norm_num at hrecip ⊢; exact hrecip
    linarith
  let C : ℝ := max 1 (2 * Real.log 2 / a)
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCpos : 0 < C := zero_lt_one.trans_le hC1
  let X : ℝ := max 2 (max (Real.log 27) (C ^ (1 / a)))
  have hX2 : 2 ≤ X := le_max_left _ _

  change ∀ D : ℝ, Real.exp X ≤ D → 2 ≤ D ^ (1 / sourceSigma D d)
  intro D hD
  have hDpos : 0 < D := (Real.exp_pos X).trans_le hD
  have hxX : X ≤ Real.log D := (Real.le_log_iff_exp_le hDpos).2 hD
  let x : ℝ := Real.log D
  have hx2 : 2 ≤ x := hX2.trans hxX
  have hxpos : 0 < x := by linarith
  have hlog27x : Real.log 27 ≤ x := by
    exact ((le_max_left (Real.log 27) (C ^ (1 / a))).trans
      (le_max_right 2 _)).trans hxX
  have hlog27D : Real.log (27 * D) = Real.log 27 + x := by
    rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) (ne_of_gt hDpos)]
  have hinner_le : Real.log (27 * D) ≤ 2 * x := by
    rw [hlog27D]
    linarith
  have hinner_pos : 0 < Real.log (27 * D) := by
    rw [hlog27D]
    have : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hll_le : Real.log (Real.log (27 * D)) ≤ 2 * Real.log x := by
    have h := Real.strictMonoOn_log.monotoneOn hinner_pos
      (show 0 < 2 * x by positivity) hinner_le
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hxpos)] at h
    have hlog2 : Real.log 2 ≤ Real.log x :=
      Real.strictMonoOn_log.monotoneOn (by norm_num) hxpos hx2
    linarith
  have hlogx : Real.log x ≤ x ^ a / a := Real.log_le_rpow_div hxpos.le ha
  have hll_bound : Real.log (Real.log (27 * D)) ≤ (2 / a) * x ^ a := by
    calc
      _ ≤ 2 * Real.log x := hll_le
      _ ≤ 2 * (x ^ a / a) := mul_le_mul_of_nonneg_left hlogx (by norm_num)
      _ = (2 / a) * x ^ a := by ring
  have hCroot : C ^ (1 / a) ≤ x := by
    exact ((le_max_right (Real.log 27) (C ^ (1 / a))).trans
      (le_max_right 2 _)).trans hxX
  have hCa : C ≤ x ^ a := by
    have hr := Real.rpow_le_rpow (Real.rpow_nonneg hCpos.le _) hCroot ha.le
    have hp : (C ^ (1 / a)) ^ a = C := by
      rw [← Real.rpow_mul hCpos.le]
      have : (1 / a) * a = 1 := by field_simp
      rw [this, Real.rpow_one]
    rwa [hp] at hr
  have htargeta : 2 * Real.log 2 / a ≤ x ^ a :=
    (le_max_right (1 : ℝ) _).trans hCa
  have hllpos : 0 < Real.log (Real.log (27 * D)) := by
    apply Real.log_pos
    rw [hlog27D]
    have : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
    linarith
  have hsigpos : 0 < sourceSigma D d := by
    unfold sourceSigma
    exact mul_pos (Real.rpow_pos_of_pos hxpos _) hllpos
  have hexponents : 1 / d + a + a = 1 := by
    dsimp [a]
    ring
  have hlog2sigma : Real.log 2 * sourceSigma D d ≤ x := by
    unfold sourceSigma
    have hnonneg : 0 ≤ Real.log 2 * x ^ (1 / d) := by positivity
    calc
      Real.log 2 * (x ^ (1 / d) * Real.log (Real.log (27 * D))) ≤
          Real.log 2 * (x ^ (1 / d) * ((2 / a) * x ^ a)) := by
            gcongr
      _ = (2 * Real.log 2 / a) * (x ^ (1 / d) * x ^ a) := by ring
      _ ≤ x ^ a * (x ^ (1 / d) * x ^ a) := by gcongr
      _ = x := by
        rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
        have he : a + (1 / d + a) = 1 := by linarith [hexponents]
        rw [he, Real.rpow_one]
  have hquot : Real.log 2 ≤ Real.log D / sourceSigma D d := by
    rw [le_div_iff₀ hsigpos]
    simpa [x, mul_comm] using hlog2sigma
  rw [Real.rpow_def_of_pos hDpos]
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact Real.exp_le_exp.mpr (by simpa [div_eq_mul_inv] using hquot)

noncomputable def sourceGeometryCutoff : ℝ :=
  max (Real.exp (Real.exp 3)) (sourceSigmaTwoCutoff 16)

theorem numerical_source_geometry {D : ℝ} (hD : sourceGeometryCutoff ≤ D) :
    3 ≤ sourceSigma D 16 ∧
      D ^ (1 / sourceSigma D 16) ≤ D ^ (1 / 3 : ℝ) ∧
      2 ≤ D ^ (1 / sourceSigma D 16) := by
  have h3 := numerical_sourceSigma_three 16 (by norm_num) D
    ((le_max_left _ _).trans hD)
  have h2 := numerical_sourceSigma_two 16 (by norm_num) D
    ((le_max_right _ _).trans hD)
  have hDone : 1 ≤ D :=
    (Real.one_le_exp (Real.exp_pos 3).le).trans ((le_max_left _ _).trans hD)
  exact ⟨h3, sourceSigma_rpow_le_cubeRoot hDone h3, h2⟩

noncomputable def recursiveCoordinateCutoff : ℝ :=
  (Real.exp (Real.exp (2 / (1 - 1 / (16 : ℝ))))) ^ (2 : ℕ)

theorem numerical_recursive_coordinate {D p : ℕ}
    (hD : recursiveCoordinateCutoff ≤ (D : ℝ))
    (hp : p.Prime) {s : ℝ} (hs : 2 ≤ s)
    (hlower : (D : ℝ)^(1 / sourceSigma (D : ℝ) 16) ≤ (p : ℝ))
    (hupper : (p : ℝ) < (D : ℝ)^(1/s)) :
    recursiveCoordinate D p ≤ sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) 16 := by
  exact recursiveCoordinate_le_quotient_sourceSigma (by norm_num : (1 : ℝ) < 16)
    hD hp hs hlower hupper

noncomputable def sourceRoundedCutoff : ℝ :=
  max sourceGeometryCutoff
    (max 8 (max (Real.exp 1) (max (Real.exp (2 * Real.log 2)) (Real.exp ((3 : ℝ)^ (16 : ℝ))))))

theorem numerical_source_rounded_geometry :
    ∀ (S : BoundingSieve) (D : ℕ), sourceRoundedCutoff ≤ (D : ℝ) →
      ∀ s : ℝ, 1 < s → s ≤ 3 →
        SourceRoundedGeometryPacket S D
          ⌈(D : ℝ)^(1/(3 : ℝ))⌉₊ ⌈(D : ℝ)^(1/s)⌉₊ 16 s := by
  let d : ℝ := 16
  let Elog : ℝ := Real.exp (2 * Real.log 2)
  let Ed : ℝ := Real.exp ((3 : ℝ) ^ d)
  let Dsize : ℝ := max 8 (max (Real.exp 1) (max Elog Ed))
  let D0 : ℝ := max sourceGeometryCutoff Dsize

  change ∀ (S : BoundingSieve) (D : ℕ), D0 ≤ (D : ℝ) → _
  intro S D hDD0 s hs1 hs3
  have hsourceGeometryCutoffD : sourceGeometryCutoff ≤ (D : ℝ) :=
    (le_max_left sourceGeometryCutoff Dsize).trans hDD0
  have hDsizeD : Dsize ≤ (D : ℝ) :=
    (le_max_right sourceGeometryCutoff Dsize).trans hDD0
  change max 8 (max (Real.exp 1) (max Elog Ed)) ≤ (D : ℝ) at hDsizeD
  simp only [max_le_iff] at hDsizeD
  rcases hDsizeD with ⟨hD8R, hExpOne, hElog, hEd⟩
  have hD8 : 8 ≤ D := by exact_mod_cast hD8R
  have hDpos : 0 < D := by omega
  have hDrealpos : 0 < (D : ℝ) := by exact_mod_cast hDpos
  have hDlarge : 2 * Real.log 2 ≤ Real.log (D : ℝ) := by
    apply (Real.le_log_iff_exp_le hDrealpos).2
    simpa [Elog] using hElog
  have h3dlog : (3 : ℝ) ^ d ≤ Real.log (D : ℝ) := by
    apply (Real.le_log_iff_exp_le hDrealpos).2
    simpa [Ed] using hEd
  obtain ⟨h3σ, hwy, hw2⟩ := numerical_source_geometry hsourceGeometryCutoffD
  let y : ℕ := ⌈(D : ℝ) ^ (1 / (3 : ℝ))⌉₊
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  have hs : 0 < s := zero_lt_one.trans hs1
  have hyceil : y = ⌈(D : ℝ) ^ (1 / (3 : ℝ))⌉₊ := rfl
  have hzceil : z = ⌈(D : ℝ) ^ (1 / s)⌉₊ := rfl
  obtain ⟨hyLower, hyUpper⟩ := natCeil_cuberoot_cubeBracket D hDpos
  have hycube : ∀ p ∈ suzukiSupportedBelow S y, p ^ 3 < D :=
    supported_cube_lt_of_eq_natCeil_cuberoot S hDpos hyceil
  have hyrzr : (D : ℝ) ^ (1 / (3 : ℝ)) ≤ (D : ℝ) ^ (1 / s) :=
    rpow_one_div_mono_of_le (by exact_mod_cast (show 1 ≤ D by omega)) hs hs3
  have hyz : y ≤ z :=
    caseII_hyz_of_natCeil_powerCutoffs (show 1 ≤ D by omega) hs hs3 hyceil hzceil
  obtain ⟨_, _, hy2, hyDhalf⟩ :=
    SwitchingPrinciple.SuzukiLemma144KappaOne.nat_cubic_cutoff_real_geometry
      hD8 hyLower hyUpper
  have hyr2 : 2 ≤ (D : ℝ) ^ (1 / (3 : ℝ)) := by
    have h8root : (8 : ℝ) ^ (1 / (3 : ℝ)) = 2 := by
      calc
        (8 : ℝ) ^ (1 / (3 : ℝ)) = (((2 : ℝ) ^ (3 : ℕ)) ^ (1 / (3 : ℝ))) := by
          norm_num
        _ = 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
    rw [← h8root]
    exact Real.rpow_le_rpow (by norm_num) hD8R (by norm_num)
  have hzr2 : 2 ≤ (D : ℝ) ^ (1 / s) := hyr2.trans hyrzr
  exact {
    h3σ := h3σ
    hD := hExpOne
    hDlarge := hDlarge
    hwy := hwy
    hy2 := hy2
    hyr2 := hyr2
    hw2 := hw2
    hycube := hycube
    hyceil := hyceil
    hyrzr := hyrzr
    hyz := hyz
    hyLower := hyLower
    hyUpper := hyUpper
    hyDhalf := hyDhalf
    hzceil := hzceil
    hzr2 := hzr2
    h3dlog := h3dlog }

#print axioms numerical_source_rounded_geometry
#print axioms numerical_source_geometry
#print axioms numerical_recursive_coordinate
end ChenEffective
