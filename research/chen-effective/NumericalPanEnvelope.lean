import NumericalPanUnweighted
import NumericalWeightedMass

noncomputable section
namespace ChenEffective
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiuWeight
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def panActualEnvelopeConstant (κ : ℝ) : ℝ := 6+liuPanLiEnvelopeConstant κ
theorem panActualEnvelopeConstant_pos (κ : ℝ) : 0 < panActualEnvelopeConstant κ := by
  unfold panActualEnvelopeConstant
  have := liuPanLiEnvelopeConstant_pos κ
  positivity

theorem numerical_pan_envelope (κ : ℝ) (N A₁ A₂ q : ℕ)
    (hN : 2 ≤ N) (hq : 0 < q) (hqN : q ≤ N) :
    (q.totient : ℝ)*liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral κ)
      N A₁ A₂ q (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) ≤
      panActualEnvelopeConstant κ*N*(1+Real.log (N : ℝ))^2 := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hpoint (l : ℕ) :
      (q.totient : ℝ)*|liuMainPanCoprimeIntervalSum (liuLogarithmicIntegral κ)
        N A₁ A₂ q l (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))| ≤
      panActualEnvelopeConstant κ*N*(1+Real.log (N : ℝ))^2 := by
    have hc := modulus_mul_liuCoprimeIntervalCount_le N (liuSourceZ10 N) (liuSourceY3 N)
      A₁ A₂ q l hq hqN
    have hcount := (mul_le_mul_of_nonneg_right hφq
      (liuCoprimeIntervalCount_nonneg N (liuSourceZ10 N) (liuSourceY3 N) A₁ A₂ q l)).trans hc
    have hm := abs_liuPanLi_mainTerm_finset_le κ N q ((Ioc A₁ A₂).filter (fun a => a.Coprime q))
    have hmain := (mul_le_mul_of_nonneg_left hm hφ.le)
    rw [mul_div_cancel₀ _ hφ.ne'] at hmain
    simp only [sum_filter, mul_div_assoc] at hmain
    have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    have ht : 1 ≤ (1+Real.log (N : ℝ))^2 := by nlinarith only [hl, sq_nonneg (Real.log (N : ℝ))]
    have ht' : 1+Real.log (N : ℝ) ≤ (1+Real.log (N : ℝ))^2 := by
      nlinarith only [hl, sq_nonneg (Real.log (N : ℝ))]
    rw [liuMainPanCoprimeIntervalSum_eq_count_sub_main]
    calc
      _ ≤ (q.totient : ℝ)*(|liuCoprimeIntervalCount N (liuSourceZ10 N) (liuSourceY3 N) A₁ A₂ q l|+
          |∑ a ∈ Ioc A₁ A₂, if a.Coprime q then liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a*
            (liuLogarithmicIntegral κ ((N : ℝ)/a)/q.totient) else 0|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) hφ.le
      _ ≤ 6*N+liuPanLiEnvelopeConstant κ*N*(1+Real.log (N : ℝ)) := by
        rw [mul_add, abs_of_nonneg (liuCoprimeIntervalCount_nonneg ..)]
        exact add_le_add hcount hmain
      _ ≤ 6*N*(1+Real.log (N : ℝ))^2+liuPanLiEnvelopeConstant κ*N*(1+Real.log (N : ℝ))^2 :=
        add_le_add (by simpa only [mul_one] using mul_le_mul_of_nonneg_left ht (by positivity : (0 : ℝ) ≤ 6*N))
          (mul_le_mul_of_nonneg_left ht' (by positivity [liuPanLiEnvelopeConstant_nonneg κ]))
      _ = _ := by unfold panActualEnvelopeConstant; ring
  unfold liuMainPanCoprimeIntervalMaxL
  dsimp only
  split
  next h =>
    apply (le_div_iff₀' hφ).mp
    apply max'_le
    intro x hx
    obtain ⟨l, _, rfl⟩ := mem_image.mp hx
    exact (le_div_iff₀' hφ).mpr (hpoint l)
  next =>
    simp only [mul_zero]
    positivity [panActualEnvelopeConstant_pos κ]

end ChenEffective
