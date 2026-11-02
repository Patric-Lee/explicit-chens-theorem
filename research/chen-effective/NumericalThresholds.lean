import MathlibNt.SieveTheory.Switching.WeightedCounting
import MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries
import MathlibNt.ChensTheorem

/-! Finite, numerical Chen endgame. No additional axioms.
The analytic lower/triple bounds remain explicit hypotheses. -/
namespace ChenEffective

open Finset Filter
open MathlibNt.SieveTheory
open SingularSeries SwitchingPrinciple

private theorem integer_product_lower (n : ℕ) :
    ((n : ℝ) + 2) / (2 * ((n : ℝ) + 1)) ≤
      ∏ p ∈ range (n + 3), (1 + liuBaseDeviation p) := by
  induction n with
  | zero => norm_num [liuBaseDeviation, Finset.prod_range_succ]
  | succ n ih =>
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hg : 1 - 1 / ((n : ℝ) + 2) ^ 2 ≤ 1 + liuBaseDeviation (n + 3) := by
      unfold liuBaseDeviation
      split_ifs
      · push_cast
        ring_nf
        norm_num
      · simp only [add_zero, sub_le_self_iff]
        positivity
    have hg0 := (one_add_liuBaseDeviation_pos (n + 3)).le
    have hr0 : 0 ≤ ((n : ℝ) + 2) / (2 * ((n : ℝ) + 1)) := by positivity
    rw [show n + 1 + 3 = (n + 3) + 1 by omega, Finset.prod_range_succ]
    calc
      _ = (((n : ℝ) + 2) / (2 * ((n : ℝ) + 1))) *
          (1 - 1 / ((n : ℝ) + 2) ^ 2) := by
        push_cast
        field_simp
        ring
      _ ≤ (((n : ℝ) + 2) / (2 * ((n : ℝ) + 1))) *
          (1 + liuBaseDeviation (n + 3)) := mul_le_mul_of_nonneg_left hg hr0
      _ ≤ _ := mul_le_mul_of_nonneg_right ih hg0

theorem half_le_liuUniversalProduct : (1 / 2 : ℝ) ≤ liuUniversalProduct := by
  have ht : Tendsto (fun n : ℕ => ∏ p ∈ range (n + 3), (1 + liuBaseDeviation p))
      atTop (nhds liuUniversalProduct) :=
    multipliable_one_add_liuBaseDeviation.tendsto_prod_tprod_nat.comp
      (Filter.tendsto_add_atTop_nat 3)
  apply ge_of_tendsto ht
  filter_upwards [] with n
  apply le_trans (b := ((n : ℝ) + 2) / (2 * ((n : ℝ) + 1))) _ (integer_product_lower n)
  apply (le_div_iff₀ (by positivity : 0 < 2 * ((n : ℝ) + 1))).mpr
  linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]

theorem half_le_liuSingularSeries (N : ℕ) : (1 / 2 : ℝ) ≤ liuSingularSeries N :=
  half_le_liuUniversalProduct.trans (liuUniversalProduct_le_liuSingularSeries N)

def errorCutoff (B : ℕ) : ℕ := 3 ^ (20000 * B + 1)
def chenCutoff (nLower nTriple B : ℕ) : ℕ :=
  max 9 (max nLower (max nTriple (errorCutoff B)))

theorem log_ge_errorCutoff {B N : ℕ} (hN : errorCutoff B ≤ N) :
    (20000 * B : ℝ) ≤ Real.log (N : ℝ) := by
  have hthree : (1 : ℝ) ≤ Real.log 3 := by
    have h := Real.log_two_gt_d9
    -- log(3) > 1 follows already from 3^2 >= 2^3 and log(2) > .69.
    have hlog' := Real.log_le_log (by norm_num : (0 : ℝ) < 8) (by norm_num : (8 : ℝ) ≤ 9)
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, show (9 : ℝ) = 3 ^ 2 by norm_num,
      Real.log_pow, Real.log_pow] at hlog'
    norm_num at hlog'
    linarith
  have hp : (0 : ℝ) < (errorCutoff B : ℕ) := by
    exact_mod_cast (show 0 < errorCutoff B by unfold errorCutoff; positivity)
  have hlog := Real.log_le_log hp
    (show (errorCutoff B : ℝ) ≤ (N : ℝ) by exact_mod_cast hN)
  have heq : Real.log (errorCutoff B : ℝ) = (20000 * (B : ℝ) + 1) * Real.log 3 := by
    simp [errorCutoff, Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_mul]
  rw [heq] at hlog
  nlinarith [show (0 : ℝ) ≤ B from Nat.cast_nonneg B]

/-- The recovered cutoff pays `C N/log^3 N` by `10^-4 S(N) N/log^2 N`. -/
theorem inverse_log_remainder_le {B N : ℕ} {C : ℝ}
    (hC : C ≤ B) (hN : errorCutoff B ≤ N) (hN9 : 9 ≤ N) :
    C * (N : ℝ) / Real.log N ^ 3 ≤
      (1 / 10000 : ℝ) * liuSingularSeries N * (N : ℝ) / Real.log N ^ 2 := by
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpay : C ≤ (1 / 10000 : ℝ) * liuSingularSeries N * Real.log N := by
    have hs := half_le_liuSingularSeries N
    have hB := log_ge_errorCutoff hN
    have hmul := mul_le_mul_of_nonneg_right hs hlog.le
    nlinarith
  apply (div_le_div_iff₀ (pow_pos hlog 3) (pow_pos hlog 2)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hpay
    (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg (Real.log (N : ℝ))))]

/-- Explicit endgame with precisely the numerical input estimates in the
recovered attempt. This does not claim numerical values for the inputs. -/
theorem explicit_representation_count
    (nLower nTriple B : ℕ) (C : ℝ) (hC : C ≤ B)
    (hLower : ∀ N : ℕ, nLower ≤ N → Even N →
      (2.6407 : ℝ) * liuSingularSeries N * (N : ℝ) / Real.log N ^ 2 ≤
        jurkatRichertWeightedCount N)
    (hTriple : ∀ N : ℕ, nTriple ≤ N → Even N →
      correctedChenTriplePenalty N ≤
        (3.94033 : ℝ) * liuSingularSeries N * (N : ℝ) / Real.log N ^ 2 +
          C * (N : ℝ) / Real.log N ^ 3)
    {N : ℕ} (hN : chenCutoff nLower nTriple B ≤ N) (hEven : Even N) :
    (0.67 : ℝ) * liuSingularSeries N * (N : ℝ) / Real.log N ^ 2 ≤
      ((chenGoodRepresentations N).card : ℝ) := by
  have hN9 : 9 ≤ N := (le_max_left _ _).trans hN
  have hNl : nLower ≤ N := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hN
  have hNt : nTriple ≤ N := by unfold chenCutoff at hN; omega
  have hNe : errorCutoff B ≤ N := by unfold chenCutoff at hN; omega
  have hl := hLower N hNl hEven
  have ht := hTriple N hNt hEven
  have he := inverse_log_remainder_le hC hNe hN9
  have hb := corrected_counting_bridge_public_of_nine_le hN9
  rw [correctedChenKeyCount_eq_jurkatRichertWeightedCount_sub_triple] at hb
  have hs : 0 ≤ liuSingularSeries N * (N : ℝ) / Real.log N ^ 2 :=
    div_nonneg (mul_nonneg (liuSingularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
  simp only [mul_div_assoc, mul_assoc] at hl ht he hs ⊢
  nlinarith only [hl, ht, he, hb, hs]

theorem explicit_chen_of_estimates
    (nLower nTriple B : ℕ) (C : ℝ) (hC : C ≤ B)
    (hLower : ∀ N : ℕ, nLower ≤ N → Even N →
      (2.6407 : ℝ) * liuSingularSeries N * (N : ℝ) / Real.log N ^ 2 ≤
        jurkatRichertWeightedCount N)
    (hTriple : ∀ N : ℕ, nTriple ≤ N → Even N →
      correctedChenTriplePenalty N ≤
        (3.94033 : ℝ) * liuSingularSeries N * (N : ℝ) / Real.log N ^ 2 +
          C * (N : ℝ) / Real.log N ^ 3)
    {N : ℕ} (hN : chenCutoff nLower nTriple B ≤ N) (hEven : Even N) :
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q = r * s) ∧ N = p + q := by
  have hc := explicit_representation_count nLower nTriple B C hC hLower hTriple hN hEven
  have hN9 : 9 ≤ N := (le_max_left _ _).trans hN
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hmain : 0 < (0.67 : ℝ) * liuSingularSeries N * (N : ℝ) / Real.log N ^ 2 := by
    apply div_pos _ (pow_pos hlog 2)
    exact mul_pos (mul_pos (by norm_num) (liuSingularSeries_pos N))
      (by exact_mod_cast (show 0 < N by omega))
  have hcard : 0 < (chenGoodRepresentations N).card := by exact_mod_cast hmain.trans_le hc
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard
  simp only [chenGoodRepresentations, Finset.mem_filter, Finset.mem_range] at hp
  refine ⟨p, N - p, hp.2.1, ?_, by omega⟩
  exact MathlibNt.ChensTheorem.semiprime_iff.mp ⟨hp.2.2.1, hp.2.2.2⟩

#print axioms explicit_chen_of_estimates
end ChenEffective
