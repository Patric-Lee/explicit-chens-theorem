import GRHArithmeticProgressions

/-! Uniformity over all prefixes, including the small-endpoint range where
the logarithmic GRH estimate is not used. The small range is elementary. -/
namespace ChenEffective.GRH
open Real Finset
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

theorem chebyshev_AP_trivial (y : ℕ) {q a : ℕ} (hq : 0 < q) :
    ‖lambdaAPMainError y q a‖ ≤ 7*(y:ℝ) := by
  classical
  have hsum : ‖lambdaAPPrefix y q a‖ ≤ Chebyshev.psi (y:ℝ) := by
    unfold lambdaAPPrefix
    calc
      _ ≤ ∑ n ∈ (Finset.range (y+1)).filter (fun n : ℕ => (n:ZMod q)=(a:ZMod q)),
          ‖lambdaNatCoeff n‖ := norm_sum_le _ _
      _ = ∑ n ∈ (Finset.range (y+1)).filter (fun n : ℕ => (n:ZMod q)=(a:ZMod q)),
          ArithmeticFunction.vonMangoldt n := by
        apply Finset.sum_congr rfl
        intro n _
        simp [lambdaNatCoeff,ArithmeticFunction.vonMangoldt_nonneg]
      _ ≤ ∑ n ∈ Finset.range (y+1), ArithmeticFunction.vonMangoldt n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
      _ = _ := by rw [Chebyshev.psi_eq_sum_range]; norm_num
  have hφ1 : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hi : (q.totient:ℝ)⁻¹ ≤ 1 := by
    simpa only [one_div,inv_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hφ1
  have hm : ‖(q.totient:ℂ)⁻¹*(y:ℂ)‖ ≤ (y:ℝ) := by
    simpa using mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg y : (0:ℝ)≤y)
  have hp := Chebyshev.psi_le_const_mul_self (by positivity : (0:ℝ)≤y)
  have hl4 : Real.log (4:ℝ) ≤ 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢
    linarith only [hh]
  unfold lambdaAPMainError
  apply (norm_sub_le _ _).trans
  have hh := mul_le_mul_of_nonneg_right hl4 (Nat.cast_nonneg y : (0:ℝ)≤y)
  nlinarith only [hsum,hp,hm,hh]

private theorem exp_ten_cap : Real.exp (10:ℝ) ≤ 59049 := by
  have he : Real.exp (1:ℝ) ≤ 3 := by linarith only [Real.exp_one_lt_d9]
  have hh := pow_le_pow_left₀ (Real.exp_pos 1).le he 10
  rw [← Real.exp_nat_mul] at hh
  norm_num at hh
  exact hh

theorem chebyshev_AP_prefix_through_numerical {N y q a : ℕ}
    (hN : 2 ≤ N) (hL : (10:ℝ) ≤ Real.log N) (hy : y ≤ N)
    (hq : 0 < q) (ha : a.Coprime q) :
    ‖lambdaAPMainError y q a‖ ≤
      (10^15:ℝ)*(Real.log q+Real.log N)^3*(N:ℝ)^(501/1000:ℝ) := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hlq : 0 ≤ Real.log (q:ℝ) := Real.log_nonneg hq1
  by_cases hly : (10:ℝ) ≤ Real.log y
  · have hy2 : 2 ≤ y := by
      by_contra hn
      have hy1 : y ≤ 1 := by omega
      interval_cases y <;> norm_num at hly
    have hy0 : (0:ℝ) < y := by exact_mod_cast (show 0 < y by omega)
    have hyN : (y:ℝ) ≤ N := by exact_mod_cast hy
    have hlmono := Real.log_le_log hy0 hyN
    have hly0 : 0 ≤ Real.log (y:ℝ) := by linarith only [hly]
    apply (chebyshev_AP_numerical hy2 hly hq ha).trans
    gcongr
  · have hySmall : (y:ℝ) < 59049 := by
      by_cases hy0 : y=0
      · subst y; norm_num
      · have hyR : (0:ℝ) < y := by exact_mod_cast (Nat.pos_of_ne_zero hy0)
        exact ((Real.log_lt_iff_lt_exp hyR).mp (not_le.mp hly)).trans_le exp_ten_cap
    have ht := chebyshev_AP_trivial (q := q) (a := a) y hq
    have hA1 : (1:ℝ) ≤ Real.log (q:ℝ)+Real.log N := by linarith only [hlq,hL]
    have hY1 : (1:ℝ) ≤ (N:ℝ)^(501/1000:ℝ) := Real.one_le_rpow hN1 (by norm_num)
    have h1 : (1:ℝ) ≤ (Real.log (q:ℝ)+Real.log N)^3*(N:ℝ)^(501/1000:ℝ) := by
      calc
        1 = (1:ℝ)*1 := by ring
        _ ≤ _ := mul_le_mul (one_le_pow₀ hA1) hY1 (by norm_num) (by positivity)
    nlinarith only [ht,hySmall,h1]

theorem chebyshev_AP_max_numerical {N q : ℕ} (hN : 2 ≤ N)
    (hL : (10:ℝ) ≤ Real.log N) (hq : 0 < q) :
    lambdaAPPrefixMaxError N q ≤
      (10^15:ℝ)*(Real.log q+Real.log N)^3*(N:ℝ)^(501/1000:ℝ) := by
  classical
  unfold lambdaAPPrefixMaxError
  apply Finset.max'_le
  intro z hz
  simp only [Finset.mem_insert,Finset.mem_image] at hz
  rcases hz with rfl | ⟨p,hp,rfl⟩
  · positivity
  · rcases Finset.mem_product.mp hp with ⟨hy,ha⟩
    have hcop : p.2.Coprime q := by
      simp [AnalyticNumberTheory.Sieve.unitResidues] at ha
      exact ha.2
    exact chebyshev_AP_prefix_through_numerical hN hL (Nat.le_of_lt_succ (Finset.mem_range.mp hy)) hq hcop

#print axioms chebyshev_AP_trivial
#print axioms chebyshev_AP_max_numerical
end ChenEffective.GRH
