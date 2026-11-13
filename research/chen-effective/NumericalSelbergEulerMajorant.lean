import NumericalSquareAssembly
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLRightHalfPlaneBounds

noncomputable section
namespace ChenEffective
open Classical Finset Filter
open scoped BigOperators
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- A finite Euler-product majorant, with its numerical exponent supplied
before taking any infinite sum. -/
theorem numerical_multiplicative_mass (f b : ℕ → ℝ) (C : ℝ)
    (hf0 : f 0 = 0) (hf1 : f 1 = 1) (hf : ∀ n, 0 ≤ f n)
    (hmul : ∀ {m n}, m.Coprime n → f (m*n)=f m*f n)
    (hloc : ∀ p, p.Prime → Summable (fun e => f (p^e)))
    (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n) (hC : (∑' n, b n) ≤ C)
    (hfactor : ∀ p, p.Prime → (∑' e, f (p^e)) ≤ Real.exp (b p)) :
    Summable f ∧ (∑' n, f n) ≤ Real.exp C := by
  have hrange : ∀ z, (∑ n ∈ range z, f n) ≤ Real.exp C := by
    intro z
    have hsmooth := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      (f := f) hf1 (fun {_ _} hmn => hmul hmn) (by
        intro p hp
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hf _)] using hloc p hp) z
    have hsind : Summable (z.smoothNumbers.indicator f) := by
      apply summable_subtype_iff_indicator.mp
      change Summable (fun n : z.smoothNumbers => f (n : ℕ))
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hf _)] using hsmooth.1
    calc
      _ = ∑ n ∈ range z, z.smoothNumbers.indicator f n := by
        apply sum_congr rfl
        intro n hn
        by_cases hn0 : n=0
        · subst n; simp [Set.indicator, hf0]
        · rw [Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hn0) (mem_range.mp hn))]
      _ ≤ ∑' n, z.smoothNumbers.indicator f n := hsind.sum_le_tsum _ (by
        intro n _
        by_cases hn : n ∈ z.smoothNumbers <;> simp [Set.indicator, hn, hf n])
      _ = ∑' n : z.smoothNumbers, f n := (_root_.tsum_subtype _ _).symm
      _ = ∏ p ∈ z.primesBelow, ∑' e, f (p^e) := hsmooth.2.tsum_eq
      _ ≤ ∏ p ∈ z.primesBelow, Real.exp (b p) := prod_le_prod₀
        (fun p _ => tsum_nonneg (fun e => hf _)) (fun p hp => hfactor p (Nat.prime_of_mem_primesBelow hp))
      _ = Real.exp (∑ p ∈ z.primesBelow, b p) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp C := Real.exp_le_exp.mpr ((hb.sum_le_tsum _ (fun n _ => hb0 n)).trans hC)
  have hs := summable_of_sum_range_le hf hrange
  exact ⟨hs,hs.tsum_le_of_sum_range_le hrange⟩

def selbergRootWeight (n : ℕ) : ℝ := |liuSelbergCorrection 2 n| * Real.sqrt (Real.sqrt n)
def selbergRootMajorant (n : ℕ) : ℝ := (if n=2 then 2 else 0)+9*(n : ℝ)^(-(3/2 : ℝ))

theorem selbergRootMajorant_summable : Summable selbergRootMajorant := by
  unfold selbergRootMajorant
  apply Summable.add
  · exact summable_of_ne_finset_zero (s := {2}) (by intro n hn; simp_all)
  · exact (Real.summable_nat_rpow.mpr (by norm_num : -(3/2 : ℝ) < -1)).mul_left 9

theorem selbergRootMajorant_mass : (∑' n, selbergRootMajorant n) ≤ 29 := by
  have hs : Summable (fun n : ℕ => if n=2 then (2 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {2}) (by intro n hn; simp_all)
  have hr := Real.summable_nat_rpow.mpr (by norm_num : -(3/2 : ℝ) < -1)
  change (∑' n : ℕ, ((if n=2 then (2 : ℝ) else 0)+9*(n : ℝ)^(-(3/2 : ℝ)))) ≤ 29
  rw [hs.tsum_add (hr.mul_left 9), tsum_mul_left]
  have hh := tsum_nat_rpow_neg_le (3/2) (by norm_num)
  norm_num only [show (3/2 : ℝ)-1=1/2 by norm_num, one_div_div, div_one] at hh
  have ht : (∑' n : ℕ, if n=2 then (2 : ℝ) else 0)=2 := by simp
  rw [ht]
  linarith only [hh]

end ChenEffective
