import NumericalDerivativeCertificate
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingClaim146iIICorrected

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
private lemma corrected_lambda_nonneg
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    {D d : ℝ} (hD : 1 < D) (sign : ErrorSign) {t : ℝ} (ht : 0 < t) :
    0 ≤ lambda H sign D d 1 t := by
  rw [lambda_eq_perturb_mul_weightedHat]
  apply mul_nonneg
  · apply Real.rpow_nonneg
    have hu : 0 ≤ (t + 1) ^ d / Real.log D :=
      div_nonneg (Real.rpow_nonneg (by linarith) _) (Real.log_pos hD).le
    linarith
  · exact mul_nonneg (sq_nonneg t) (hH.positive sign t ht).le

noncomputable def claim146MonotoneCutoff : ℝ :=
  max derivativeCutoff
    (Real.exp (max 1 (((1 + 4 * (16 : ℝ)) * 5^(16 : ℝ)) / ((1 + (1/2 : ℝ))/12))))

theorem numerical_claim146_monotone {H : Section13HatLayers}
    (hSource : Section13HatSourceContract H) :
    ∀ D : ℝ, claim146MonotoneCutoff ≤ D →
      Claim14_6_MonotoneLambdaPremise H D 16 (sourceSigma D 16) ∧
      Claim14_6_MonotoneQPremise H D 16 (1/2) (sourceSigma D 16) := by
  let d : ℝ := 16
  let Δ : ℝ := 1/2
  have hd1 : 1 < d := by norm_num [d]
  have hΔ : -1 < Δ := by norm_num [Δ]
  have hH := hSource.toSection13HatContract
  let Da := derivativeCutoff
  have hDa : 1 < Da := derivativeCutoff_gt_one
  have hcert := fun (D : ℝ) (hD : Da ≤ D) => numerical_derivative_certificate hSource hD
  let ρ : ℝ := (1 + Δ) / 12
  let C : ℝ := (1 + 4 * d) * 5 ^ d
  have hρ : 0 < ρ := by
    dsimp [ρ]
    have : 0 < 1 + Δ := by linarith
    exact div_pos this (by norm_num)
  have hC : 0 ≤ C := by
    dsimp [C]
    have hfactor : 0 ≤ 1 + 4 * d := by linarith
    exact mul_nonneg hfactor (Real.rpow_nonneg (by norm_num) _)
  let X : ℝ := max 1 (C / ρ)
  let Db : ℝ := Real.exp X
  have hX : 0 < X := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hDb : 1 < Db := by
    dsimp [Db]
    exact Real.one_lt_exp_iff.mpr hX
  let D₀ : ℝ := max Da Db
  change ∀ D : ℝ, D₀ ≤ D → _
  intro D hD
  have hDaD : Da ≤ D := (le_max_left Da Db).trans hD
  have hDbD : Db ≤ D := (le_max_right Da Db).trans hD
  have hD1 : 1 < D := hDa.trans_le hDaD
  have hlog : 0 < Real.log D := Real.log_pos hD1
  rcases hcert D hDaD with ⟨hσ4, hdom⟩
  have hXD : X ≤ Real.log D := by
    apply (Real.le_log_iff_exp_le (zero_lt_one.trans hD1)).2
    simpa [Db] using hDbD
  have hClog : C ≤ ρ * Real.log D := by
    have hCrho : C / ρ ≤ X := le_max_right _ _
    have := hCrho.trans hXD
    simpa [mul_comm] using (div_le_iff₀ hρ).mp this
  have hi : Claim14_6_MonotoneLambdaPremise H D d (sourceSigma D d) :=
    claim14_6_i_of_explicit_derivative_domination hH hlog hdom
  have hi' := hi
  unfold Claim14_6_MonotoneLambdaPremise at hi'
  rw [hH.betaHat_eq] at hi'
  refine ⟨hi, ?_⟩
  unfold Claim14_6_MonotoneQPremise
  rw [hH.betaHat_eq]
  intro sign
  cases sign with
  | plus =>
      have hshift : AntitoneOn
          (fun t => lambda H ErrorSign.minus D d 1 (t - 1))
          (Ioc (2 + 1) (sourceSigma D d)) := by
        intro x hx y hy hxy
        apply hi' ErrorSign.minus 1 (Or.inr rfl)
        · constructor
          · simp [ErrorSign.epsilon]; linarith [hx.1]
          · linarith [hx.2]
        · constructor
          · simp [ErrorSign.epsilon]; linarith [hy.1]
          · linarith [hy.2]
        · linarith
      apply qD_mul_antitoneOn_of_shifted_lambda H ErrorSign.plus D d Δ hΔ.le
        (S := Ioc (2 + 1) (sourceSigma D d))
      · intro t ht
        change 1 < t
        have ht3 : 3 < t := by norm_num at ht ⊢; exact ht.1
        linarith
      · exact hshift
      · intro t ht
        exact corrected_lambda_nonneg hH hD1 ErrorSign.minus (by linarith [ht.1])
  | minus =>
      have hlargeFixed : (1 + 4 * d) * (4 + 1) ^ d ≤ ρ * Real.log D := by
        norm_num [C] at hClog ⊢
        exact hClog
      have hshortFixed : ρ * (4 * (4 - 1)) ≤ 1 + Δ := by
        dsimp [ρ]
        ring_nf
        exact le_rfl
      have hlow : AntitoneOn
          (fun t => qD H ErrorSign.plus D d Δ t * t) (Ioc 2 4) := by
        exact qD_mul_antitoneOn_short_minus
          (H := H) (β := 2) (D := D) (d := d) (Δ := Δ)
          (τ := 4) (σ := 4) (ρ := ρ) hH (by linarith) hΔ.le hρ hlog
          hlargeFixed (by norm_num) (by norm_num) le_rfl hshortFixed
      have hshift : AntitoneOn
          (fun t => lambda H ErrorSign.plus D d 1 (t - 1))
          (Icc 4 (sourceSigma D d)) := by
        intro x hx y hy hxy
        apply hi' ErrorSign.plus 1 (Or.inr rfl)
        · constructor
          · simp [ErrorSign.epsilon]; linarith [hx.1]
          · linarith [hx.2]
        · constructor
          · simp [ErrorSign.epsilon]; linarith [hy.1]
          · linarith [hy.2]
        · linarith
      have hhigh : AntitoneOn
          (fun t => qD H ErrorSign.plus D d Δ t * t)
          (Icc 4 (sourceSigma D d)) := by
        apply qD_mul_antitoneOn_of_shifted_lambda H ErrorSign.minus D d Δ hΔ.le
        · intro t ht
          change 1 < t
          have ht4 : 4 ≤ t := ht.1
          linarith
        · exact hshift
        · intro t ht
          exact corrected_lambda_nonneg hH hD1 ErrorSign.plus (by linarith [ht.1])
      intro x hx y hy hxy
      simp [ErrorSign.epsilon] at hx hy
      by_cases hy4 : y ≤ 4
      · exact hlow ⟨hx.1, hxy.trans hy4⟩ ⟨hy.1, hy4⟩ hxy
      · have h4y : 4 ≤ y := (lt_of_not_ge hy4).le
        by_cases hx4 : x ≤ 4
        · exact (hhigh ⟨le_rfl, hσ4⟩ ⟨h4y, hy.2⟩ h4y).trans
            (hlow ⟨hx.1, hx4⟩ ⟨by norm_num, le_rfl⟩ hx4)
        · exact hhigh ⟨(lt_of_not_ge hx4).le, hx.2⟩ ⟨h4y, hy.2⟩ hxy
#print axioms numerical_claim146_monotone
end ChenEffective
