import BJSHybridWeightedBridge
import BJSHybridZeroSplit
import BJSHybridPrimePowers

noncomputable section
namespace ChenEffective.HybridProduct
open Complex.Hadamard
open Real Set MeasureTheory
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def slopeCoefficient (L : ℝ) : ℝ := 2/L+3/L^2+2/L^3

theorem prefix_slope_nonneg {x : ℝ} (hx : 1 < x) : 0 ≤ prefixSlope x := by
  have hl := log_pos hx
  unfold prefixSlope
  positivity

theorem prefix_weight_nonneg {x : ℝ} (hx : 1 < x) : 0 ≤ prefixWeight x := by
  have hl := log_pos hx
  unfold prefixWeight
  positivity

theorem prefix_slope_bound {a t : ℝ} (ha : 1 < a) (hat : a ≤ t) :
    prefixSlope t ≤ slopeCoefficient (log a)*t^(-3:ℝ) := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have ht0 : 0 < t := ha0.trans_le hat
  have hla : 0 < log a := log_pos ha
  have hlt : 0 < log t := hla.trans_le (log_le_log ha0 hat)
  have hlog := log_le_log ha0 hat
  have h1 := one_div_le_one_div_of_le hla hlog
  have h2 := one_div_le_one_div_of_le (pow_pos hla 2)
    (pow_le_pow_left₀ hla.le hlog 2)
  have h3 := one_div_le_one_div_of_le (pow_pos hla 3)
    (pow_le_pow_left₀ hla.le hlog 3)
  have hc : slopeCoefficient (log t) ≤ slopeCoefficient (log a) := by
    unfold slopeCoefficient
    simp only [div_eq_mul_inv, one_mul] at h1 h2 h3 ⊢
    linarith only [h1,h2,h3]
  have he : prefixSlope t = slopeCoefficient (log t)*t^(-3:ℝ) := by
    rw [rpow_neg ht0.le,rpow_ofNat]
    unfold prefixSlope slopeCoefficient
    field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_right hc (rpow_nonneg ht0.le _)

theorem psi1_error_envelope (H : Finset DusartXiZero) {x W : ℝ}
    (hx : 1 < x) (hline : ∀ p ∈ H,(divisorZeroIndex₀_val p).re=1/2)
    (hW : (∑' p : {p : DusartXiZero // p ∉ H},absoluteXiWeight p) ≤ W) :
    |psi1Error x| ≤ (3/25)*x^(3/2:ℝ)+W*x^(15/8:ℝ)+2*x+1000000000 := by
  exact actual_psi1_split_envelope H hx hline hW

/-- Pointwise domination preserves each exponent in the integrated envelope. -/
theorem psi1_slope_envelope (H : Finset DusartXiZero) {a t W : ℝ}
    (ha : 1 < a) (hat : a ≤ t)
    (hline : ∀ p ∈ H,(divisorZeroIndex₀_val p).re=1/2)
    (hW : (∑' p : {p : DusartXiZero // p ∉ H},absoluteXiWeight p) ≤ W) :
    |psi1Error t*prefixSlope t| ≤ slopeCoefficient (log a)*
      ((3/25)*t^(-3/2:ℝ)+W*t^(-9/8:ℝ)+2*t^(-2:ℝ)+1000000000*t^(-3:ℝ)) := by
  have ht : 1 < t := ha.trans_le hat
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hW0 : 0 ≤ W := (tsum_nonneg (fun _ => norm_nonneg _)).trans hW
  have hF := psi1_error_envelope H ht hline hW
  have hS := prefix_slope_bound ha hat
  rw [abs_mul,abs_of_nonneg (prefix_slope_nonneg ht)]
  calc
    _ ≤ ((3/25)*t^(3/2:ℝ)+W*t^(15/8:ℝ)+2*t+1000000000)*
        (slopeCoefficient (log a)*t^(-3:ℝ)) :=
      mul_le_mul hF hS (prefix_slope_nonneg ht) (by positivity)
    _ = _ := by
      have h1 : t^(3/2:ℝ)*t^(-3:ℝ)=t^(-3/2:ℝ) := by
        rw [← rpow_add ht0]; norm_num
      have h2 : t^(15/8:ℝ)*t^(-3:ℝ)=t^(-9/8:ℝ) := by
        rw [← rpow_add ht0]; norm_num
      have h3 : t*t^(-3:ℝ)=t^(-2:ℝ) := by
        calc
          _ = t^(1:ℝ)*t^(-3:ℝ) := by rw [rpow_one]
          _ = _ := by rw [← rpow_add ht0]; norm_num
      linear_combination slopeCoefficient (log a)*((3/25)*h1+W*h2+2*h3)

#print axioms psi1_slope_envelope
end ChenEffective.HybridProduct


