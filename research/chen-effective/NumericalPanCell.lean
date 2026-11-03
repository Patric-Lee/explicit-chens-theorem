import NumericalPanLong
import NumericalPanQuotient
import MathlibNt.AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducerHighAggregate

open Classical Complex Finset Filter MeasureTheory
open scoped BigOperators
namespace ChenEffective.NumericalPanHigh
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

noncomputable def panShortConstant : ℝ := 16*panSharpConstant
noncomputable def panLongConstant : ℝ := 16*panSharpConstant*(1+2/Real.log 2)
noncomputable def panCellConstant : ℝ := 36*panShortConstant+36*Real.exp 2*panLongConstant
@[irreducible] def panHighThreshold (B : ℕ) : ℕ := logPowerCutoff (6*B)

theorem numerical_high_log_four {B N : ℕ} (hN : panHighThreshold B ≤ N) :
    4 ≤ Real.log (N : ℝ) := by
  unfold panHighThreshold at hN
  have hh := log_power_cutoff_log hN
  have hb := Nat.cast_nonneg (α := ℝ) (6*B)
  nlinarith only [hh, hb, sq_nonneg ((6*B : ℕ) : ℝ)]

theorem numerical_source_power {B N : ℕ} (hN : panHighThreshold B ≤ N) :
    (N : ℝ)^(2/3 : ℝ) ≤ upperConductor N (B : ℝ)^2 := by
  have hL := numerical_high_log_four hN
  have hl0 : 0 < Real.log (N : ℝ) := by linarith only [hL]
  have hn := hN
  unfold panHighThreshold at hn
  have hN9 : 9 ≤ N := (logPowerCutoff_nine_le _).trans hn
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp := log_pow_le_rpow_inv_explicit (k := 2*B) (m := 3)
    (by norm_num) (by omega : 3*(2*B) ≤ 6*B) hn
  have heq : lowConductor N (B : ℝ)^2 = Real.log (N : ℝ)^(2*B) := by
    rw [lowConductor, Real.rpow_natCast, ← pow_mul, Nat.mul_comm B 2]
  rw [upperConductor_square, le_div_iff₀ (by unfold lowConductor; positivity), heq]
  calc
    _ ≤ (N : ℝ)^(2/3 : ℝ) * (N : ℝ)^(1/3 : ℝ) :=
      mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hN0.le _)
    _ = _ := by rw [← Real.rpow_add hN0]; norm_num

theorem numerical_source_cell_uniform (B N : ℕ) (hN : panHighThreshold B ≤ N)
    (j m A₁ A₂ k : ℕ) (f : ℕ → ℂ) (hAN : A₂ ≤ N)
    (hRD : conductorRadius N (B : ℝ) j ≤ upperConductor N (B : ℝ))
    (hA : (A₂ : ℝ) ≤ (N : ℝ)^(2/3 : ℝ))
    (hAlow : Real.log (N : ℝ)^((2 : ℝ)*B) ≤ A₁)
    (hf : ∀ n, ‖f n‖ ≤ 1) :
    sourceCell f m N A₁ A₂ k (conductorRadius N (B : ℝ) j) ≤
      6*liuPanPerronHalfStep N^(1/2 : ℝ)*
        (panShortConstant*Real.sqrt N*Real.log N^(1-(B : ℝ)))*Real.log (1+panSourceHeight N) +
      6*liuPanPerronHalfStep N^panSourceSigma N*
        (panLongConstant*Real.log N^2/Real.log N^(B : ℝ))*Real.log (1+panSourceHeight N) +
      776/(N : ℝ) := by
  have hlog := numerical_high_log_four hN
  have hl1 : 1 ≤ Real.log (N : ℝ) := by linarith only [hlog]
  have hNpos : 1 ≤ N := source_pos_of_log hl1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hR := conductorRadius_ge_one j hl1 (Nat.cast_nonneg B)
  have hH := shortCutoff_le_x hl1 (Nat.cast_nonneg B) (by linarith only [hR]) hRD
  obtain ⟨_, rfl, _, hlong⟩ := chosen_long_mean_uniform
  have hmain := source_cell_bound_of_means f hf m A₁ A₂ k hlog hNpos le_rfl hAN hR hH
    (show 0 ≤ panShortConstant*Real.sqrt N*Real.log N^(1-(B : ℝ)) by
      unfold panShortConstant; have hh := panSharpConstant_pos; positivity)
    (show 0 ≤ panLongConstant*Real.log N^2/Real.log N^(B : ℝ) by
      unfold panLongConstant; have hh := panSharpConstant_pos; positivity)
    (fun s hs => shortMean_le_log_scale f hf m A₁ A₂ k N (Nat.cast_nonneg B) hl1 hR hRD
      (hA.trans (numerical_source_power hN)) s hs)
    (fun s hs => hlong (B : ℝ) N N j m A₁ A₂ k f s (Nat.cast_nonneg B) hl1 le_rfl hAlow hf hs)
  apply hmain.trans
  apply add_le_add le_rfl
  have hRx : conductorRadius N (B : ℝ) j ≤ (N : ℝ) :=
    hRD.trans ((upperConductor_le_sqrt hl1 (Nat.cast_nonneg B)).trans
      (Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast hNpos))))
  calc
    _ ≤ 2*(N : ℝ)*(388/(N : ℝ)^2) := by gcongr
    _ = _ := by field_simp; norm_num

#print axioms numerical_source_cell_uniform
end ChenEffective.NumericalPanHigh
