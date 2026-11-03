import NumericalPanCell

noncomputable section
open Classical Complex Finset Filter
open scoped BigOperators
namespace ChenEffective.NumericalPanHigh
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem numerical_source_cell_log_saving (B x : ℕ) (hx : panHighThreshold B ≤ x)
    (j m A₁ A₂ k : ℕ) (f : ℕ → ℂ)
    (hAx : A₂ ≤ x) (hRD : conductorRadius x (B : ℝ) j ≤ upperConductor x (B : ℝ))
    (hApower : (A₂ : ℝ) ≤ (x : ℝ)^(2/3 : ℝ))
    (hAlow : Real.log (x : ℝ)^((2 : ℝ)*B) ≤ A₁) (hf : ∀ n, ‖f n‖ ≤ 1) :
    sourceCell f m x A₁ A₂ k (conductorRadius x (B : ℝ) j) ≤
      panCellConstant * x * Real.log x^(4-(B : ℝ)) + 776/(x : ℝ) := by
  have hxlog := numerical_high_log_four hx
  have hCs : 0 < panShortConstant := by unfold panShortConstant; exact mul_pos (by norm_num) panSharpConstant_pos
  have hCl : 0 < panLongConstant := by unfold panLongConstant; have := panSharpConstant_pos; positivity
  have hxlog1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hxpos := source_pos_of_log hxlog1
  have hxone : (1 : ℝ) ≤ x := by exact_mod_cast hxpos
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  have hmain := numerical_source_cell_uniform B x hx j m A₁ A₂ k f hAx hRD hApower hAlow hf
  have hsqrt : liuPanPerronHalfStep x ^ (1 / 2 : ℝ) ≤ 2 * Real.sqrt x := by
    rw [← Real.sqrt_eq_rpow]
    have hsq := Real.sq_sqrt (halfStep_pos x).le
    have hxq := Real.sq_sqrt hx0.le
    have hp := Real.sqrt_nonneg (liuPanPerronHalfStep x)
    have hxp := Real.sqrt_nonneg (x : ℝ)
    unfold liuPanPerronHalfStep at hsq hp ⊢
    nlinarith
  have hlogT := log_source_height_le hxlog1
  have hlognonneg : 0 ≤ Real.log (1 + panSourceHeight x) :=
    Real.log_nonneg (by have : 0 < panSourceHeight x := Real.exp_pos _; linarith)
  have hshort :
      6 * liuPanPerronHalfStep x ^ (1 / 2 : ℝ) *
          (panShortConstant * Real.sqrt x * Real.log x ^ (1 - (B : ℝ))) * Real.log (1 + panSourceHeight x) ≤
        36 * panShortConstant * (x : ℝ) * Real.log x ^ (4 - (B : ℝ)) := by
    calc
      _ ≤ 6 * (2 * Real.sqrt x) * (panShortConstant * Real.sqrt x * Real.log x ^ (1 - (B : ℝ))) *
          (3 * (Real.log x) ^ 2) := by gcongr
      _ = 36 * panShortConstant * (x : ℝ) * Real.log x ^ (3 - (B : ℝ)) := by
        rw [show (3 - (B : ℝ) : ℝ) = (1 - (B : ℝ)) + 2 by ring, Real.rpow_add hlogpos,
          Real.rpow_two]
        calc
          _ = 36 * panShortConstant * (Real.sqrt (x : ℝ)) ^ 2 *
              (Real.log x ^ (1 - (B : ℝ)) * (Real.log x) ^ 2) := by ring
          _ = _ := by rw [Real.sq_sqrt hx0.le]
      _ ≤ _ := by
        gcongr
        norm_num
  have hlong :
      6 * liuPanPerronHalfStep x ^ panSourceSigma x *
          (panLongConstant * (Real.log x) ^ 2 / Real.log x ^ (B : ℝ)) * Real.log (1 + panSourceHeight x) ≤
        (36 * Real.exp 2 * panLongConstant) * (x : ℝ) * Real.log x ^ (4 - (B : ℝ)) := by
    calc
      _ ≤ 6 * (2 * Real.exp 2 * (x : ℝ)) *
          (panLongConstant * (Real.log x) ^ 2 / Real.log x ^ (B : ℝ)) * (3 * (Real.log x) ^ 2) := by
        gcongr
        exact halfStep_source_power_le_linear hxlog hxpos le_rfl
      _ = _ := by
        rw [Real.rpow_sub hlogpos, Real.rpow_ofNat]
        ring
  refine hmain.trans (add_le_add (add_le_add hshort hlong) le_rfl |>.trans ?_)
  exact le_of_eq (by unfold panCellConstant; ring)


theorem numerical_high_source_depth_saving (B x : ℕ) (hx : panHighThreshold B ≤ x)
    (m A₁ A₂ : ℕ) (f : ℕ → ℂ) (hAx : A₂ ≤ x)
    (hApower : (A₂ : ℝ) ≤ (x : ℝ)^(2/3 : ℝ))
    (hAlow : Real.log (x : ℝ)^((2 : ℝ)*B) ≤ A₁) (hf : ∀ n, ‖f n‖ ≤ 1) :
    panIymHigh (panSourceG f m) (panSourceD m) x A₁ A₂
      ⌊lowConductor x (B : ℝ)⌋₊ ⌊upperConductor x (B : ℝ)⌋₊ ≤
    (Nat.log 2 x + 1 : ℝ)^2 *
      (panCellConstant*x*Real.log x^(4-(B : ℝ)) + 776/(x : ℝ)) := by
  have hxlog := numerical_high_log_four hx
  have hC : 0 < panCellConstant := by
    unfold panCellConstant panShortConstant panLongConstant
    have := panSharpConstant_pos
    positivity
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hxlog1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hA₁ : 0 < A₁ := by
    have hp : (0 : ℝ) < Real.log x ^ ((2 : ℝ) * B) :=
      Real.rpow_pos_of_pos (by linarith only [hxlog]) _
    have : (0 : ℝ) < A₁ := hp.trans_le hAlow
    exact_mod_cast this
  let M := panCellConstant * (x : ℝ) * Real.log x ^ (4 - (B : ℝ)) + 776 / (x : ℝ)
  have hM : 0 ≤ M := by
    dsimp [M]
    have : 0 ≤ Real.log (x : ℝ) := by linarith
    positivity
  let s := (range (Nat.log 2 x + 1)).filter
    (fun j => conductorRadius x (B : ℝ) j ≤ upperConductor x (B : ℝ))
  have hs : s.card ≤ Nat.log 2 x + 1 :=
    (card_filter_le _ _).trans_eq (card_range _)
  calc
    _ ≤ ∑ j ∈ s, ∑ k ∈ range (panDyadicDepth A₁ A₂),
        sourceCell f m x A₁ A₂ k (conductorRadius x (B : ℝ) j) :=
      panIymHigh_le_sum_active_sourceCells f m x A₁ A₂ B hxlog1 hB hA₁
    _ ≤ ∑ j ∈ s, ∑ _k ∈ range (panDyadicDepth A₁ A₂), M := by
      apply sum_le_sum
      intro j hj
      apply sum_le_sum
      intro k hk
      exact numerical_source_cell_log_saving B x hx j m A₁ A₂ k f hAx
        (mem_filter.mp hj).2 hApower hAlow hf
    _ = (s.card : ℝ) * (panDyadicDepth A₁ A₂ : ℝ) * M := by simp; ring
    _ ≤ (Nat.log 2 x + 1 : ℝ) * (Nat.log 2 x + 1 : ℝ) * M := by
      gcongr
      · exact_mod_cast hs
      · exact_mod_cast source_depth_le (A₁ := A₁) hAx
    _ = _ := by rw [pow_two]

noncomputable def panHighConstant : ℝ := 9*panCellConstant

theorem numerical_high_source_log_saving (B x : ℕ) (hx : panHighThreshold B ≤ x)
    (m A₁ A₂ : ℕ) (f : ℕ → ℂ) (hAx : A₂ ≤ x)
    (hApower : (A₂ : ℝ) ≤ (x : ℝ)^(2/3 : ℝ))
    (hAlow : Real.log (x : ℝ)^((2 : ℝ)*B) ≤ A₁) (hf : ∀ n, ‖f n‖ ≤ 1) :
    panIymHigh (panSourceG f m) (panSourceD m) x A₁ A₂
      ⌊lowConductor x (B : ℝ)⌋₊ ⌊upperConductor x (B : ℝ)⌋₊ ≤
    panHighConstant*x*Real.log x^(6-(B : ℝ)) + 6984*Real.log x^2/(x : ℝ) := by
  have hxlog := numerical_high_log_four hx
  have hC : 0 < panCellConstant := by
    unfold panCellConstant panShortConstant panLongConstant
    have := panSharpConstant_pos
    positivity
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  calc
    _ ≤ (Nat.log 2 x + 1 : ℝ) ^ 2 *
        (panCellConstant * (x : ℝ) * Real.log x ^ (4 - (B : ℝ)) + 776 / (x : ℝ)) :=
      numerical_high_source_depth_saving B x hx m A₁ A₂ f hAx hApower hAlow hf
    _ ≤ (3 * Real.log x) ^ 2 *
        (panCellConstant * (x : ℝ) * Real.log x ^ (4 - (B : ℝ)) + 776 / (x : ℝ)) := by
      gcongr
      exact log_depth_le_three_log hxlog
    _ = _ := by
      rw [show (6 - (B : ℝ) : ℝ) = 2 + (4 - (B : ℝ)) by ring, Real.rpow_add hlogpos,
        Real.rpow_two]
      unfold panHighConstant
      ring


#print axioms numerical_high_source_log_saving
end ChenEffective.NumericalPanHigh
