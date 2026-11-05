import QualitativeTriple

noncomputable section
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory SingularSeries SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
set_option exponentiation.threshold 512

/-- Separate existence cutoff. The established 0.67 counting cutoff is untouched. -/
def qualitativeN0 : ℕ := qualitativeGeometryThreshold
theorem qualitativeN0_eq : qualitativeN0=3^(3^6000) := qualitativeGeometryThreshold_eq

theorem qualitative_inverse_log_payment {N : ℕ} (hN : qualitativeN0 ≤ N) :
    (numericalTripleErrorCap : ℝ)*N/log (N : ℝ)^3 ≤
      (1/2 : ℝ)*liuSingularSeries N*N/log (N : ℝ)^2 := by
  obtain ⟨hN2,_⟩ := qualitative_endpoint_parameters hN
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hcap : preSieveFiniteCap ≤ preSieveFiniteCap^20 := by
    simpa only [pow_one] using Nat.pow_le_pow_right preSieve_H_one_nat (show 1 ≤ 20 by norm_num)
  have h1 : preSieveFiniteCap ≤ N := hcap.trans (qualitative_finite_cap.trans hN)
  have hpow : 3^(4*numericalTripleErrorCap+1) ≤ N :=
    (preSieve_fixed_power (by norm_num [numericalTripleErrorCap])).trans h1
  have hlog := log_ge_power_three hpow
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hlog
  have hs := half_le_liuSingularSeries N
  have hpay : (numericalTripleErrorCap : ℝ) ≤ (1/2)*liuSingularSeries N*log (N : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hs hl.le
    nlinarith only [hh,hlog]
  apply (div_le_div_iff₀ (pow_pos hl 3) (pow_pos hl 2)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hpay
    (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg (log (N : ℝ))))]

/-- Direct positive-margin proof of qualitative Chen. Neither the 0.67 count
theorem nor its tiny error budget is used. -/
theorem qualitative_chen {N : ℕ} (hN : qualitativeN0 ≤ N) (hEven : Even N) :
    ∃ p q : ℕ, p.Prime ∧ (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q := by
  obtain ⟨hN2,_⟩ := qualitative_endpoint_parameters hN
  have hN9 : 9 ≤ N := by
    have hEnd := qualitative_endpoint hN
    have hh : 2^110+1 ≤ N := (le_max_left _ _).trans hEnd
    omega
  have hl := qualitative_weighted_lower hN hEven
  have ht := qualitative_triple_bound hN hEven
  have he := qualitative_inverse_log_payment hN
  have hb := corrected_counting_bridge_public_of_nine_le hN9
  rw [correctedChenKeyCount_eq_jurkatRichertWeightedCount_sub_triple] at hb
  let M := liuSingularSeries N*N/log (N : ℝ)^2
  have hM : 0 < M := by
    dsimp [M]
    exact div_pos (mul_pos (liuSingularSeries_pos N) (by exact_mod_cast (show 0 < N by omega)))
      (pow_pos (log_pos (by exact_mod_cast (show 1 < N by omega))) 2)
  have hcount : (1/20 : ℝ)*M ≤ ((chenGoodRepresentations N).card : ℝ) := by
    dsimp only [M]
    simp only [mul_div_assoc,mul_assoc] at hl ht he hM ⊢
    nlinarith only [hl,ht,he,hb,hM.le]
  have hcard : 0 < (chenGoodRepresentations N).card := by
    exact_mod_cast (mul_pos (by norm_num : (0 : ℝ) < 1/20) hM).trans_le hcount
  obtain ⟨p,hp⟩ := Finset.card_pos.mp hcard
  simp only [chenGoodRepresentations,Finset.mem_filter,Finset.mem_range] at hp
  refine ⟨p,N-p,hp.2.1,?_,by omega⟩
  exact MathlibNt.ChensTheorem.semiprime_iff.mp ⟨hp.2.2.1,hp.2.2.2⟩

#print axioms qualitative_chen
end ChenEffective
