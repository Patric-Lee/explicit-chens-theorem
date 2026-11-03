import NumericalPrimePairGrid
import NumericalGenuineLiPointwise

noncomputable section
namespace ChenEffective
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory
open LiuWeight
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000

theorem numerical_prime_pair_reciprocal {N : ℕ} (hN : primePairThreshold ≤ N) :
    liuWeightPairReciprocalSum N ≤ 1 := by
  obtain ⟨hN9,hlog,_,_⟩ := numerical_prime_pair_parameters hN
  have hL0 : 0 < Real.log (N : ℝ) := by linarith only [hlog]
  have hsum : liuWeightPairReciprocalSum N ≤ liuPairLogKernelSum N := by
    apply sum_le_sum
    intro p hp
    have hpp : (0 : ℝ) < (p.1 : ℝ)*p.2 := by exact_mod_cast liuWeightPairs_product_pos hp
    have hden := one_sub_primeLogExponent_pos (by omega : 8 ≤ N) hp
    have ha0 : 0 ≤ primeLogExponent N p.1 := div_nonneg (Real.log_natCast_nonneg _) hL0.le
    have hb0 : 0 ≤ primeLogExponent N p.2 := div_nonneg (Real.log_natCast_nonneg _) hL0.le
    apply one_div_le_one_div_of_le (mul_pos hpp hden)
    nlinarith only [mul_nonneg hpp.le ha0,mul_nonneg hpp.le hb0]
  rw [← log_mul_liuSourceReciprocalLogSum_eq_pairLogKernelSum N (by omega)] at hsum
  exact hsum.trans ((numerical_prime_pair_proxy hN).trans (by norm_num))

theorem numerical_genuine_li_sum {N : ℕ} (hN : primePairThreshold ≤ N) :
    |liuGenuineLiRemainderSum 2 N| ≤ (1 : ℝ)/100000000*N/Real.log (N : ℝ) := by
  obtain ⟨hN9,hlog,_,hcut⟩ := numerical_prime_pair_parameters hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL0 : 0 < Real.log (N : ℝ) := by linarith only [hlog]
  have hpair : ∀ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
      |liuLogarithmicIntegralRemainder 2 ((N : ℝ)/(p.1*p.2))| ≤
        9*10*(N : ℝ)/(((p.1 : ℝ)*p.2)*Real.log (N : ℝ)^2) := by
    intro p hp
    apply liuLogarithmicIntegralRemainder_pair_le 2 10 (by norm_num) N (by omega) p hp
    apply numerical_genuine_li_pointwise
    have hpp : (0 : ℝ) < (p.1 : ℝ)*p.2 := by exact_mod_cast liuWeightPairs_product_pos hp
    have hx0 : 0 < (N : ℝ)/((p.1 : ℝ)*p.2) := div_pos hN0 hpp
    have hxlog := one_third_mul_log_le_log_div_of_mem_liuWeightPairs (by omega : 8 ≤ N) hp
    have hroot : (N : ℝ)^(1/10 : ℝ) ≤ (N : ℝ)/((p.1 : ℝ)*p.2) := by
      apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hN0 _) hx0).mp
      rw [Real.log_rpow hN0]
      linarith only [hxlog,hL0]
    exact hcut.trans hroot
  have hsum : |liuGenuineLiRemainderSum 2 N| ≤ 90*(N : ℝ)/Real.log (N : ℝ)^2 := by
    unfold liuGenuineLiRemainderSum
    calc
      _ ≤ ∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
          |liuLogarithmicIntegralRemainder 2 ((N : ℝ)/(p.1*p.2))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
          9*10*(N : ℝ)/(((p.1 : ℝ)*p.2)*Real.log (N : ℝ)^2) := sum_le_sum hpair
      _ = (9*10*(N : ℝ)/Real.log (N : ℝ)^2)*liuWeightPairReciprocalSum N :=
        liuGenuineLiRemainderSum_factor 10 N
      _ ≤ (9*10*(N : ℝ)/Real.log (N : ℝ)^2)*1 :=
        mul_le_mul_of_nonneg_left (numerical_prime_pair_reciprocal hN) (by positivity)
      _ = _ := by ring
  apply hsum.trans
  apply (div_le_div_iff₀ (sq_pos_of_pos hL0) hL0).mpr
  have hcoef : (90 : ℝ) ≤ Real.log (N : ℝ)/100000000 := by
    norm_num at hlog ⊢
    linarith only [hlog]
  have hh := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ (N : ℝ)*Real.log (N : ℝ) by positivity)
  nlinarith only [hh]

theorem numerical_prime_pair_main {N : ℕ} (hN : primePairThreshold ≤ N) :
    LiuGenuineLiWeightMainSumBound 2 (0.49254+liuM1Eta) N := by
  obtain ⟨hN9,hlog,_,_⟩ := numerical_prime_pair_parameters hN
  have hL0 : 0 < Real.log (N : ℝ) := by linarith only [hlog]
  have hsrc := numerical_prime_pair_proxy hN
  have hrem := numerical_genuine_li_sum hN
  have hproxy : liuWeightMainSum (fun x : ℝ => x/Real.log x) N ≤
      ((0.49254 : ℝ)+2/100000000)*N/Real.log (N : ℝ) := by
    rw [liuWeightMainSum_div_log_eq N (by omega)]
    apply (le_div_iff₀ hL0).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hsrc (Nat.cast_nonneg (α := ℝ) N)]
  refine ⟨liuWeightMainSum_logarithmicIntegral_nonneg 2 (by norm_num) N (by omega),?_⟩
  rw [liuWeightMainSum_logarithmicIntegral_eq_proxy_add_remainder]
  have htail := (le_abs_self (liuGenuineLiRemainderSum 2 N)).trans hrem
  have hNn : 0 ≤ (N : ℝ)/Real.log (N : ℝ) := by positivity
  simp only [div_eq_mul_inv] at hproxy htail hNn ⊢
  norm_num only [liuM1Eta]
  nlinarith only [hproxy,htail,hNn]

#print axioms numerical_prime_pair_main
end ChenEffective
