import GRHPrimeRootMoment

/-! Sharper pre-sieve moment, using the logarithm of each block endpoint.
No prime enumeration, new analytic hypothesis, or external dependency. -/
noncomputable section
namespace ChenEffective.GRH
open Real Finset
set_option maxHeartbeats 3000000

theorem log_lower_of_two_power (k a : ℕ) (ell : ℝ)
    (hpow : 2^k ≤ a) (hell : ell ≤ (k:ℝ)*(693/1000)) :
    ell ≤ log (a:ℝ) := by
  have ha : (0:ℝ) < a := by exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < 2^k) hpow)
  have hlog := log_le_log (by positivity : (0:ℝ)<(2:ℝ)^k)
    (show (2:ℝ)^k ≤ a by exact_mod_cast hpow)
  rw [log_pow] at hlog
  have hk := mul_le_mul_of_nonneg_left (le_of_lt log_two_gt_d9) (Nat.cast_nonneg k)
  nlinarith only [hlog,hk,hell,(show (0:ℝ)≤(k:ℝ) from Nat.cast_nonneg k)]

theorem prime_root_block_log (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime)
    (a b : ℕ) (ell : ℝ) (ha : 0<a) (hell : 0<ell)
    (hlog : ell ≤ log (a:ℝ)) :
    (∑ p ∈ F.filter (fun p => a < p ∧ p ≤ b), 1/sqrt (p:ℝ)) ≤
      ((7/5:ℝ)*b)/(ell*sqrt (a:ℝ)) := by
  have hh := prime_root_interval (F.filter (fun p => a < p ∧ p ≤ b))
    (a:=(a:ℝ)) (b:=(b:ℝ)) (ell:=ell)
    (by exact_mod_cast ha) (Nat.cast_nonneg b) hell (by
      intro p hp
      have hpF := (mem_filter.mp hp).1
      have hpi := (mem_filter.mp hp).2
      refine ⟨hF p hpF,?_,?_,?_⟩
      · exact_mod_cast (Nat.le_of_lt hpi.1)
      · exact_mod_cast hpi.2
      · apply hlog.trans
        apply log_le_log (by exact_mod_cast ha)
        exact_mod_cast (Nat.le_of_lt hpi.1))
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg b)
  rw [show (4:ℝ)=2^2 by norm_num,log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [log_two_lt_d9]

theorem prime_root_moment_four_million_sharp (F : Finset ℕ)
    (hF : ∀ p ∈ F, p.Prime ∧ p ≤ 4000000) :
    (∑ p ∈ F, 1/sqrt (p:ℝ)) ≤ 1173 := by
  have hsmall := reciprocal_sqrt_subset (F.filter (fun p => p ≤ 10000)) 10000
    (by intro p hp; exact ⟨(hF p (mem_filter.mp hp).1).1.one_lt.le,(mem_filter.mp hp).2⟩)
  have h1 := prime_root_block_log F (fun p hp => (hF p hp).1) 10000 40000 9 (by norm_num) (by norm_num) (log_lower_of_two_power 13 10000 9 (by norm_num) (by norm_num))
  have h2 := prime_root_block_log F (fun p hp => (hF p hp).1) 40000 160000 10 (by norm_num) (by norm_num) (log_lower_of_two_power 15 40000 10 (by norm_num) (by norm_num))
  have h3 := prime_root_block_log F (fun p hp => (hF p hp).1) 160000 640000 11 (by norm_num) (by norm_num) (log_lower_of_two_power 16 160000 11 (by norm_num) (by norm_num))
  have h4 := prime_root_block_log F (fun p hp => (hF p hp).1) 640000 2560000 13 (by norm_num) (by norm_num) (log_lower_of_two_power 19 640000 13 (by norm_num) (by norm_num))
  have h5 := prime_root_block_log F (fun p hp => (hF p hp).1) 2560000 4000000 14 (by norm_num) (by norm_num) (log_lower_of_two_power 21 2560000 14 (by norm_num) (by norm_num))
  norm_num only [Nat.cast_ofNat] at hsmall h1 h2 h3 h4 h5
  have hsplit : (∑ p ∈ F, 1/sqrt (p:ℝ)) =
      (∑ p ∈ F.filter (fun p => p ≤ 10000), 1/sqrt (p:ℝ)) +
      (∑ p ∈ F.filter (fun p => 10000 < p ∧ p ≤ 40000), 1/sqrt (p:ℝ)) +
      (∑ p ∈ F.filter (fun p => 40000 < p ∧ p ≤ 160000), 1/sqrt (p:ℝ)) +
      (∑ p ∈ F.filter (fun p => 160000 < p ∧ p ≤ 640000), 1/sqrt (p:ℝ)) +
      (∑ p ∈ F.filter (fun p => 640000 < p ∧ p ≤ 2560000), 1/sqrt (p:ℝ)) +
      (∑ p ∈ F.filter (fun p => 2560000 < p ∧ p ≤ 4000000), 1/sqrt (p:ℝ)) := by
    simp only [sum_filter]
    repeat rw [← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    have hpmax := (hF p hp).2
    split_ifs
    all_goals first | omega | simp only [add_zero,zero_add]
  rw [hsplit]
  norm_num at hsmall h1 h2 h3 h4 h5
  simp only [one_div]
  linarith only [hsmall,h1,h2,h3,h4,h5]


#print axioms prime_root_moment_four_million_sharp
end ChenEffective.GRH
