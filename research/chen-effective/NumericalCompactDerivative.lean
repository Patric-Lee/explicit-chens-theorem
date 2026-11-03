import NumericalForwardEnvelope
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingDerivativeDDECompactRange

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable def legacyCompactDerivativeFloor (m : ℕ) : ℝ :=
  min (1/4) (compactHatLower m) / (2 * (m : ℝ))

theorem legacyCompactDerivativeFloor_pos {m : ℕ} (hm : 3 ≤ m) :
    0 < legacyCompactDerivativeFloor m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  exact div_pos (lt_min (by norm_num) (compactHatLower_pos hm)) (by positivity)

theorem legacy_compactDerivativeRatio_lower {H : Section13HatLayers}
    (hH : Section13HatContract H 2) {m : ℕ} (hm : 3 ≤ m)
    (sign : ErrorSign) {t : ℝ} (ht : t ∈ Icc (2 : ℝ) m) :
    legacyCompactDerivativeFloor m ≤ compactDerivativeRatio H sign t := by
  let b : ℝ := min (1/4) (compactHatLower m)
  have hb : 0 ≤ b := (lt_min (by norm_num) (compactHatLower_pos hm)).le
  have ht0 : 0 < t := by linarith only [ht.1]
  have hu : 1 ≤ t-1 := by linarith only [ht.1]
  have hT : b ≤ H.T sign.opposite (t-1) := by
    by_cases hu2 : 2 ≤ t-1
    · exact (min_le_right _ _).trans
        (numerical_hat_compact hH hm sign.opposite hu2 (by linarith only [ht.2]))
    · have hu0 : 0 < t-1 := by linarith only [hu]
      have hu2' : t-1 ≤ 2 := (lt_of_not_ge hu2).le
      have heq : 1 ≤ weightedHat H sign.opposite (t-1) := by
        cases sign <;> simp only [ErrorSign.opposite]
        · rw [hH.initial_minus _ hu0 hu2']; norm_num
        · rw [hH.initial_plus _ hu0 (by linarith only [hu2'])]; norm_num
      have hpos := (hH.positive sign.opposite _ hu0).le
      have hsq : (t-1)^2 ≤ (4 : ℝ) := by nlinarith only [hu, hu2']
      have hh := mul_le_mul_of_nonneg_right hsq hpos
      dsimp [weightedHat] at heq
      exact (min_le_left _ _).trans (by nlinarith only [hh, heq])
  have hupper := numerical_hat_upper_two hH sign (show 1 ≤ t by linarith only [ht.1])
  have hW0 : 0 < weightedHat H sign t :=
    mul_pos (sq_pos_of_pos ht0) (hH.positive sign t ht0)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  unfold compactDerivativeRatio
  apply (le_div_iff₀ hW0).mpr
  change (b / (2 * (m : ℝ))) * (t^2 * H.T sign t) ≤ t * H.T sign.opposite (t-1)
  have hsmall : b / (2 * (m : ℝ)) * (t * H.T sign t) ≤ b := by
    have hth : t * H.T sign t ≤ 2 * (m : ℝ) :=
      (mul_le_mul_of_nonneg_left hupper ht0.le).trans (by linarith only [ht.2])
    have hh := mul_le_mul_of_nonneg_left hth
      (div_nonneg hb (show 0 ≤ 2 * (m : ℝ) by positivity))
    simpa only [div_mul_cancel₀ b (show (2 : ℝ) * m ≠ 0 by positivity)] using hh
  calc
    _ = t * (b / (2 * (m : ℝ)) * (t * H.T sign t)) := by ring
    _ ≤ t * b := mul_le_mul_of_nonneg_left hsmall ht0.le
    _ ≤ _ := mul_le_mul_of_nonneg_left hT ht0.le

/-- Only a fixed short head uses an absolute minimum. At all larger coordinates
adjacent hats are compared directly, giving a polynomial reciprocal. -/
noncomputable def compactDerivativeFloor (m : ℕ) : ℝ := 1/(51200000000*(m : ℝ))

theorem compactDerivativeFloor_pos {m : ℕ} (hm : 3 ≤ m) : 0 < compactDerivativeFloor m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  unfold compactDerivativeFloor
  positivity

theorem numerical_compactDerivativeRatio_lower {H : Section13HatLayers}
    (hH : Section13HatSourceContract H) {m : ℕ} (hm : 3 ≤ m)
    (sign : ErrorSign) {t : ℝ} (ht : t ∈ Icc (2 : ℝ) m) :
    compactDerivativeFloor m ≤ compactDerivativeRatio H sign t := by
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith only [hm3]
  have ht0 : 0 < t := by linarith only [ht.1]
  by_cases ht4 : t ≤ 4
  · have hh := legacy_compactDerivativeRatio_lower hH.toSection13HatContract
      (show 3 ≤ (4 : ℕ) by norm_num) sign ⟨ht.1,ht4⟩
    apply le_trans _ hh
    unfold compactDerivativeFloor
    calc
      _ ≤ 1/(51200000000*(3 : ℝ)) := one_div_le_one_div_of_le (by norm_num) (by linarith only [hm3])
      _ ≤ legacyCompactDerivativeFloor 4 := by norm_num [legacyCompactDerivativeFloor,compactHatLower]
  have h4 : 4 < t := lt_of_not_ge ht4
  have hu0 : 0 < t-1 := by linarith only [h4]
  have hprev0 := (hH.toSection13HatContract.positive sign.opposite (t-1) hu0).le
  have hcur0 := (hH.toSection13HatContract.positive sign.opposite t ht0).le
  have hmono := weightedHat_antitoneOn_Icc_closed hH.toSection13HatContract sign.opposite
    (s := t-1) (M := t) (by cases sign <;> norm_num [ErrorSign.opposite,ErrorSign.epsilon] <;> linarith only [h4])
  have hw := hmono ⟨le_rfl,by linarith⟩ ⟨by linarith,le_rfl⟩ (by linarith : t-1 ≤ t)
  have hprev : H.T sign.opposite t ≤ H.T sign.opposite (t-1) := by
    unfold weightedHat at hw
    have hh := mul_le_mul_of_nonneg_right (show (t-1)^2 ≤ t^2 by nlinarith only [h4]) hprev0
    nlinarith only [hw,hh,sq_pos_of_pos ht0]
  have hsum : H.T sign t ≤ section13Qhat H t := by
    unfold section13Qhat
    have hp := (hH.toSection13HatContract.positive .plus t ht0).le
    have hn := (hH.toSection13HatContract.positive .minus t ht0).le
    cases sign <;> linarith only [hp,hn]
  have hcomp : H.T sign t ≤ 51200000000*H.T sign.opposite (t-1) :=
    hsum.trans ((numerical_Qhat_le_hat hH sign.opposite (by linarith only [h4])).trans
      (mul_le_mul_of_nonneg_left hprev (by norm_num)))
  have hW0 : 0 < weightedHat H sign t :=
    mul_pos (sq_pos_of_pos ht0) (hH.toSection13HatContract.positive sign t ht0)
  unfold compactDerivativeRatio
  apply (le_div_iff₀ hW0).mpr
  unfold compactDerivativeFloor weightedHat
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (show (0 : ℝ) < 51200000000*m by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_left hcomp (sq_nonneg t)
  have hh' := mul_le_mul_of_nonneg_right ht.2 (mul_nonneg ht0.le hprev0)
  nlinarith only [hh,hh']

noncomputable def compactDerivativeCutoff (m : ℕ) (d : ℝ) : ℝ :=
  Real.exp (max 1 (((1 + (m : ℝ) * d) * ((m : ℝ) + 1)^d) / compactDerivativeFloor m))

theorem numerical_compact_derivative {H : Section13HatLayers}
    (hH : Section13HatSourceContract H) {m : ℕ} (hm : 3 ≤ m) {d : ℝ} (hd : 0 ≤ d) :
    ∀ D : ℝ, compactDerivativeCutoff m d ≤ D →
      ∀ (sign : ErrorSign) (ε t : ℝ),
        (ε=0 ∨ ε=1) → 2 + sign.epsilon < t → t ≤ m →
        weightedHat H sign t * perturbationSlope D d ε t ≤
          t * H.T sign.opposite (t-1) := by
  intro D hD sign ε t hε ht hMt
  have hf := compactDerivativeFloor_pos hm
  have hD0 : 0 < D := (Real.exp_pos _).trans_le hD
  have hlogLarge : max 1 (((1 + (m : ℝ) * d) * ((m : ℝ)+1)^d) /
      compactDerivativeFloor m) ≤ Real.log D := (Real.le_log_iff_exp_le hD0).mpr hD
  have hlog : 0 < Real.log D := zero_lt_one.trans_le ((le_max_left _ _).trans hlogLarge)
  have hCm := (le_max_right _ _).trans hlogLarge
  have hC : (1 + (m : ℝ) * d) * ((m : ℝ)+1)^d ≤ compactDerivativeFloor m * Real.log D :=
    by simpa only [mul_comm] using (div_le_iff₀ hf).mp hCm
  have ht2 : 2 ≤ t := by
    cases sign <;> simp only [ErrorSign.epsilon] at ht <;> linarith only [ht]
  have ht1 : 1 ≤ t := by linarith only [ht2]
  have hε0 : 0 ≤ ε := by rcases hε with rfl | rfl <;> norm_num
  have hε1 : ε ≤ 1 := by rcases hε with rfl | rfl <;> norm_num
  have hslope : perturbationSlope D d ε t ≤ compactDerivativeFloor m :=
    (perturbationSlope_le hlog hd ht1 hMt hε0 hε1).trans
      ((div_le_iff₀ hlog).mpr (by simpa only [mul_comm] using hC))
  have hratio := numerical_compactDerivativeRatio_lower hH hm sign ⟨ht2, hMt⟩
  have ht0 : 0 < t := by linarith only [ht2]
  have hWpos : 0 < weightedHat H sign t :=
    mul_pos (sq_pos_of_pos ht0) (hH.toSection13HatContract.positive sign t ht0)
  calc
    _ ≤ weightedHat H sign t * compactDerivativeRatio H sign t :=
      mul_le_mul_of_nonneg_left (hslope.trans hratio) hWpos.le
    _ = _ := by unfold compactDerivativeRatio; field_simp [hWpos.ne']

#print axioms numerical_compact_derivative
end ChenEffective
