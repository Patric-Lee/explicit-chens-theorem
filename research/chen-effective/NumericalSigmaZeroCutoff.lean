import NumericalSourceGeometry

open scoped Classical BigOperators Interval
open Set Filter Finset Topology MeasureTheory intervalIntegral
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LinearSieve MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144Equation1410
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

noncomputable def sigmaZeroC1 : ℝ := max caseBSourceC1 (Real.log (Real.exp (Real.exp 3)))
theorem numerical_sigma_zero_cutoff
    (H : Section13HatLayers)
    {d Δ Θ : ℝ}
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hTheta : 1 ≤ Θ)
    (hH : Section13HatSourceContract H) (hd16 : d = 16) (hΔhalf : Δ = 1/2) (hΘ7 : Θ = 7) :
    ∃ C1min : ℝ, C1min = sigmaZeroC1 ∧ 0 < C1min ∧
      ∀ S : BoundingSieve, ∀ (C1 C K : ℝ) (N D z : ℕ),
        C1min ≤ C1 → (1 : ℝ) ≤ C → 2 ≤ K →
        HasDimensionOneLocalProductBound S K → 2 ≤ D →
        C1 * K ^ Θ < Real.log (D : ℝ) → 2 ≤ N →
        (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (z : ℝ) →
        suzukiSigmaZero S N D z
            ((D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)) ≤
          (1 / C) * (C * claim14_5Scale S H N (D : ℝ) d Δ
            (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d)) := by
  subst d Δ Θ
  let d : ℝ := 16
  let Δ : ℝ := 1/2
  let Θ : ℝ := 7
  let C1B := caseBSourceC1
  have hC1B : 0 < C1B := by unfold C1B caseBSourceC1; positivity
  have hcaseB := numerical_caseB_cutoff H hH
  let CB : ℝ := 1
  have hCB : 0 < CB := zero_lt_one
  let D3 : ℝ := Real.exp (Real.exp 3)
  have hD3 : 1 < D3 := Real.one_lt_exp_iff.mpr (Real.exp_pos 3)
  have hsigma3 := numerical_sourceSigma_three d (by norm_num [d])
  let C1min : ℝ := max C1B (Real.log D3)
  have hC1min : 0 < C1min := hC1B.trans_le (le_max_left _ _)
  refine ⟨C1min, rfl, hC1min, ?_⟩
  intro S C1 C K N D z hC1 hCBC hK hlocal hD hlarge hN hz
  have hC1B' : C1B ≤ C1 := (le_max_left _ _).trans hC1
  have hlogD3 : Real.log D3 ≤ Real.log (D : ℝ) := by
    calc
      Real.log D3 ≤ C1min := le_max_right _ _
      _ ≤ C1 := hC1
      _ ≤ C1 * K ^ Θ := by
        have hC10 : 0 ≤ C1 := hC1min.le.trans hC1
        have hKpow : 1 ≤ K ^ Θ :=
          Real.one_le_rpow (by linarith) (by linarith)
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hKpow hC10
      _ ≤ Real.log (D : ℝ) := hlarge.le
  have hD3D : D3 ≤ (D : ℝ) := by
    have hexp := Real.exp_le_exp.mpr hlogD3
    rw [Real.exp_log (by linarith : 0 < D3),
      Real.exp_log (by positivity : 0 < (D : ℝ))] at hexp
    exact hexp
  have hσ3 : 3 ≤ sourceSigma (D : ℝ) d := hsigma3 _ hD3D
  have hendpoint : ActualClaim145BoundAt S H N D d Δ K
      (sourceSigma (D : ℝ) d) CB :=
    hcaseB S C1 K N D (sourceSigma (D : ℝ) d)
      hC1B' hK hlocal hD (by linarith [hσ3]) hlarge le_rfl
  have hDpos : 0 < D := by omega
  have hEq := suzukiSigmaZero_eq_actualT_sourceSigma_strict
    (S := S) (N := N) (D := D) (z := z) (d := d) hN hz (by
      intro _ p hp
      exact cube_lt_of_lt_natCeil_rpow hDpos hσ3 rfl hp)
  rw [hEq]
  unfold ActualClaim145BoundAt at hendpoint
  have hCpos : 0 < C := hCB.trans_le hCBC
  calc
    suzukiActualT S N D ⌈(D : ℝ) ^
          (1 / sourceSigma (D : ℝ) d)⌉₊ ≤
        CB * claim14_5Scale S H N (D : ℝ) d Δ
          (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d) := hendpoint
    _ = (CB / C) * (C * claim14_5Scale S H N (D : ℝ) d Δ
          (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d)) := by
      field_simp [ne_of_gt hCpos]
#print axioms numerical_sigma_zero_cutoff
theorem numerical_sigma_zero_even_cutoff
    (H : Section13HatLayers)
    {d Δ Θ : ℝ}
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hTheta : 1 ≤ Θ)
    (hH : Section13HatSourceContract H) (hd16 : d=16) (hΔhalf : Δ=1/2) (hΘ7 : Θ=7) :
    ∃ C1min : ℝ, C1min = sigmaZeroC1 ∧ 0 < C1min ∧
      ∀ S : BoundingSieve, ∀ (C1 C K : ℝ) (N D z : ℕ),
        C1min ≤ C1 → (1 : ℝ) ≤ C → 2 ≤ K →
        HasDimensionOneLocalProductBound S K → 2 ≤ D →
        C1 * K ^ Θ < Real.log (D : ℝ) → Even N → 2 ≤ N →
        (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (z : ℝ) →
        suzukiSigmaZero S N D z
            ((D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)) ≤
          (1 / C) * (C * claim14_5Scale S H N (D : ℝ) d Δ
            (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d)) := by
  obtain ⟨C1min, heq, hC1min, hstrict⟩ :=
    numerical_sigma_zero_cutoff H hΔ0 hΔ1 hd hTheta hH hd16 hΔhalf hΘ7
  refine ⟨C1min, heq, hC1min, ?_⟩
  intro S C1 C K N D z hC1 hCBC hK hlocal hD hlarge _hEven hN hz
  exact hstrict S C1 C K N D z hC1 hCBC hK hlocal hD hlarge hN hz
end ChenEffective
