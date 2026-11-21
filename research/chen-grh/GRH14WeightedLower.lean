import GRH14MediumAggregate
import ChenBudget

noncomputable section
namespace ChenEffective.GRH14
open Real
open MathlibNt.SieveTheory SwitchingPrinciple
variable [Fact HybridProduct.HybridPrefixWindow]
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

omit [Fact HybridProduct.HybridPrefixWindow] in
theorem endpoint_payment_at_target {N : ℕ} (hN : targetCutoff ≤ N) :
    60*(N:ℝ)^(9/10:ℝ) ≤ (1/20000:ℝ)*
      (SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2) := by
  have hL := target_log_lower hN
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by have := (lower_endpoint_parameters hN).1; omega)
  have hp := truncated_polynomial_payment hL (A:=(60:ℝ)) (by norm_num)
    (α:=(1/10:ℝ)) (by norm_num) (k:=2) (by norm_num)
  have hid : (N:ℝ)^(9/10:ℝ)=(N:ℝ)*exp (-(1/10:ℝ)*log (N:ℝ)) := by
    calc
      _ = exp (log (N:ℝ)*(9/10:ℝ)) := rpow_def_of_pos hn _
      _ = exp (log (N:ℝ))*exp (-(1/10:ℝ)*log (N:ℝ)) := by
        rw [← exp_add]
        congr 1
        ring
      _ = _ := by rw [exp_log hn]
  have hfirst : 60*(N:ℝ)^(9/10:ℝ) ≤ (1e-6:ℝ)*((N:ℝ)/log (N:ℝ)^2) := by
    calc
      _ = ((60:ℝ)*(log (N:ℝ))^2*exp (-(1/10:ℝ)*log (N:ℝ)))*
          ((N:ℝ)/log (N:ℝ)^2) := by rw [hid]; field_simp [hl.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (by positivity)
  have hs := half_le_liuSingularSeries N
  have hc : (1e-6:ℝ) ≤ (1/20000:ℝ)*SingularSeries.liuSingularSeries N := by linarith only [hs]
  have hh := mul_le_mul_of_nonneg_right hc (show 0 ≤ (N:ℝ)/log (N:ℝ)^2 by positivity)
  apply hfirst.trans
  convert hh using 1 <;> ring

omit [Fact HybridProduct.HybridPrefixWindow] in
theorem source_boundary_at_target {N : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N) :
    jurkatRichertSourceWeightedCount N ≤ jurkatRichertWeightedCount N+
      (1/20000:ℝ)*(SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2) := by
  have hsmall : (2:ℕ)^110+1 ≤ 3^100 := by norm_num
  have hpower : (3:ℕ)^100 ≤ targetCutoff := by
    rw [targetCutoff_eq]
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hbig : (2:ℕ)^110<N := by have hh := hsmall.trans (hpower.trans hN); omega
  have hb := jurkatRichertSourceWeightedCount_sub_boundary_le_distinct N hbig hEven
  have hp := jurkatRichertDistinctWeightedCount_sub_proper_le N hbig hEven
  have he := endpoint_payment_at_target hN
  have hn : 0 ≤ (N:ℝ)^(9/10:ℝ) := rpow_nonneg (Nat.cast_nonneg N) _
  nlinarith only [hb,hp,he,hn]

theorem weighted_lower_of_window {N : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N) :
    (2.02575:ℝ)*(SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2) ≤
      jurkatRichertWeightedCount N := by
  let b : ChenBudget := ⟨3/50,111/100,1/20000,0,0⟩
  have hh := chen_budget_weighted b (base_candidates_at_target hN hEven)
    (medium_aggregate_at_target hN hEven) (source_boundary_at_target hN hEven)
  convert hh using 1
  norm_num [b,ChenBudget.weighted]

#print axioms weighted_lower_of_window
end ChenEffective.GRH14
