import BJSStudyInputs
import NumericalGoldbachInterval
import DusartPort.Application

namespace ChenEffective
open Real Finset
open MathlibNt.SieveTheory.SwitchingPrinciple
open AnalyticNumberTheory.Mertens
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

private lemma goldbach_local_factor_pos {p : ℕ} (hp2 : 2 < p) :
    0 < 1 - 1 / ((p : ℝ) - 1) := by
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp2
  have hrec : 1 / ((p : ℝ) - 1) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  linarith

/-- For an odd prime, the logarithm of the inverse Goldbach local factor is
controlled by its reciprocal-prime main term and a summable error. -/
private lemma log_goldbach_inverse_factor_le {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    log (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤
      1 / (p : ℝ) + 12 / (p : ℝ) ^ 2 := by
  have hp3 : 3 ≤ p := by omega
  have hpm1 : 0 < (p : ℝ) - 1 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    linarith
  have ht : 0 < 1 / ((p : ℝ) - 1) := div_pos one_pos hpm1
  have htle : 1 / ((p : ℝ) - 1) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    have : (2 : ℝ) ≤ (p : ℝ) - 1 := by
      have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      linarith
    linarith
  have hlocal := AnalyticNumberTheory.Mertens.abs_log_one_sub_add_le ht htle
  have hlog :
      log (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤
        1 / ((p : ℝ) - 1) + 2 * (1 / ((p : ℝ) - 1)) ^ 2 := by
    rw [Real.log_inv]
    have := (abs_le.mp hlocal).1
    nlinarith
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpm1ne : (p : ℝ) - 1 ≠ 0 := ne_of_gt hpm1
  have hmain :
      1 / ((p : ℝ) - 1) + 2 * (1 / ((p : ℝ) - 1)) ^ 2 ≤
        1 / (p : ℝ) + 12 / (p : ℝ) ^ 2 := by
    have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    field_simp [hp0, hpm1ne]
    nlinarith [sq_nonneg ((p : ℝ) - 3)]
  exact hlog.trans hmain

noncomputable def bjsStudyPresieveStart : ℝ := (3:ℝ)^(120:ℕ)

theorem bjsStudy_interval_product (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) (u z : ℝ)
    (hu : bjsStudyPresieveStart ≤ u) (huz : u ≤ z)
    (hinterval : ∀ p ∈ s, u ≤ (p : ℝ) ∧ (p : ℝ) < z) :
    (∏ p ∈ s, (1-1/((p : ℝ)-1))⁻¹) ≤ (1+(1/4000:ℝ))*(log z/log u) := by
  have hU : (286:ℝ) ≤ bjsStudyPresieveStart := by norm_num [bjsStudyPresieveStart]
  have hu1 : 1 < u := by linarith only [hU,hu]
  have hlu : 0 < log u := log_pos hu1
  have hlz : 0 < log z := log_pos (hu1.trans_le huz)
  have hlog : (120:ℝ) ≤ log u := by
    have h := log_le_log (by norm_num [bjsStudyPresieveStart] : 0 < bjsStudyPresieveStart) hu
    rw [bjsStudyPresieveStart,log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    nlinarith only [h,one_le_log_three]
  have hr := dusart_sharp_prime_interval s u z hu huz
    (fun p hp => ⟨(hs p hp).1,(hinterval p hp).1,(hinterval p hp).2.le⟩)
  let k : ℕ := 3^100
  let n : ℕ := s.sup id
  have hk : ∀ p ∈ s, k < p := by
    intro p hp
    have hh : (k:ℝ) < u := by
      have hh' : (k:ℝ) < bjsStudyPresieveStart := by norm_num [k,bjsStudyPresieveStart]
      exact hh'.trans_le hu
    exact_mod_cast hh.trans_le (hinterval p hp).1
  have hsq : (∑ p ∈ s, 1/(p:ℝ)^2) ≤ 2/(k:ℝ) := by
    calc
      _ ≤ ∑ p ∈ Finset.Ioo k (n+1), 1/(p:ℝ)^2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          exact Finset.mem_Ioo.mpr ⟨hk p hp,Nat.lt_succ_of_le (Finset.le_sup (f:=id) hp)⟩
        · intro p _ _; positivity
      _ ≤ 2/((k:ℝ)+1) := by
        simpa only [one_div] using (sum_Ioo_inv_sq_le (α:=ℝ) k (n+1))
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num [k]) (by linarith)
  have herr : 1/(log u)^2+12*(2/(k:ℝ)) ≤ (1/8000:ℝ) := by
    have hsqlog : (120:ℝ)^2 ≤ (log u)^2 := by nlinarith only [hlog]
    have hdiv := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
      (by norm_num : (0:ℝ) < 120^2) hsqlog
    norm_num [k] at hdiv ⊢
    linarith only [hdiv]
  have hprod : 0 < ∏ p ∈ s, (1-1/((p:ℝ)-1))⁻¹ :=
    Finset.prod_pos (fun p hp => inv_pos.mpr (goldbach_local_factor_pos (hs p hp).2))
  have hlprod : log (∏ p ∈ s, (1-1/((p:ℝ)-1))⁻¹) ≤
      log (log z/log u)+(1/8000:ℝ) := by
    rw [Real.log_prod (fun p hp => (inv_pos.mpr (goldbach_local_factor_pos (hs p hp).2)).ne')]
    have hh := Finset.sum_le_sum (s:=s) (fun p hp => log_goldbach_inverse_factor_le (hs p hp).1 (hs p hp).2)
    simp only [Finset.sum_add_distrib,div_eq_mul_inv,← Finset.mul_sum] at hh
    have ht := mul_le_mul_of_nonneg_left hsq (by norm_num : (0:ℝ) ≤ 12)
    simp only [div_eq_mul_inv,← Finset.mul_sum] at ht hr
    simp only [div_eq_mul_inv,one_mul] at hh ht hr herr ⊢
    linarith only [hh,ht,hr,herr]
  have he := (abs_le.mp (Real.abs_exp_sub_one_le (by norm_num : |(1/8000:ℝ)| ≤ 1))).2
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 1/8000)] at he
  have hh := exp_le_exp.mpr hlprod
  rw [exp_log hprod,exp_add,exp_log (div_pos hlz hlu)] at hh
  exact hh.trans (by nlinarith only [he,div_pos hlz hlu])

theorem bjsStudy_presieved_product (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p)
    (hpresieve : ∀ p ∈ s, bjsStudyPresieveStart ≤ (p : ℝ))
    (u z : ℝ) (hu : 1 < u) (huz : u ≤ z)
    (hinterval : ∀ p ∈ s, u ≤ (p : ℝ) ∧ (p : ℝ) < z) :
    (∏ p ∈ s, (1-1/((p : ℝ)-1))⁻¹) ≤ (1+(1/4000:ℝ))*(log z/log u) := by
  by_cases hUu : bjsStudyPresieveStart ≤ u
  · exact bjsStudy_interval_product s hs u z hUu huz hinterval
  have huU : u ≤ bjsStudyPresieveStart := le_of_not_ge hUu
  have hlu : 0 < log u := log_pos hu
  have hlz : 0 < log z := log_pos (hu.trans_le huz)
  by_cases hzU : z ≤ bjsStudyPresieveStart
  · have hempty : s=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      linarith only [hpresieve p hp,(hinterval p hp).2,hzU]
    rw [hempty,Finset.prod_empty]
    have hr : 1 ≤ log z/log u := (le_div_iff₀ hlu).mpr
      (by simpa using log_le_log (by linarith only [hu] : 0 < u) huz)
    nlinarith only [hr,(by norm_num : (0:ℝ) ≤ 1/4000)]
  have hUz : bjsStudyPresieveStart ≤ z := le_of_not_ge hzU
  apply (bjsStudy_interval_product s hs bjsStudyPresieveStart z le_rfl hUz
    (fun p hp => ⟨hpresieve p hp,(hinterval p hp).2⟩)).trans
  apply mul_le_mul_of_nonneg_left _ (by linarith only [(by norm_num : (0:ℝ) ≤ 1/4000)])
  exact div_le_div_of_nonneg_left hlz.le hlu (log_le_log (by linarith only [hu] : 0 < u) huU)


theorem bjsStudy_product_relative (S : BoundingSieve)
    (hodd : ∀ p ∈ S.prodPrimes.primeFactors, 2 < p)
    (hnu : ∀ p ∈ S.prodPrimes.primeFactors, S.nu p=1/((p : ℝ)-1)) :
    HasRelativeSieveProduct (preSieveCounting S bjsStudyPresieveStart) (1/4000:ℝ) := by
  intro u z hu huz
  unfold suzukiLocalRatio
  change (∏ p ∈ (restrictSievePrimes S bjsStudyPresieveStart).prodPrimes.primeFactors.filter
    (fun p : ℕ => u ≤ (p : ℝ) ∧ (p : ℝ) < z), (1-S.nu p)⁻¹) ≤ _
  rw [restrictSievePrimes_primeFactors]
  let s := (S.prodPrimes.primeFactors.filter (fun p : ℕ => bjsStudyPresieveStart ≤ (p : ℝ))).filter
    (fun p : ℕ => u ≤ (p : ℝ) ∧ (p : ℝ) < z)
  have hs : ∀ p ∈ s, p.Prime ∧ 2 < p := by
    intro p hp
    have hP := (mem_filter.mp (mem_filter.mp hp).1).1
    exact ⟨Nat.prime_of_mem_primeFactors hP,hodd p hP⟩
  have hid : (∏ p ∈ s, (1-S.nu p)⁻¹) = ∏ p ∈ s, (1-1/((p : ℝ)-1))⁻¹ := by
    apply prod_congr rfl
    intro p hp
    rw [hnu p (mem_filter.mp (mem_filter.mp hp).1).1]
  change (∏ p ∈ s, (1-S.nu p)⁻¹) ≤ _
  rw [hid]
  exact bjsStudy_presieved_product s hs (fun _ hp => (mem_filter.mp (mem_filter.mp hp).1).2)
    u z hu huz (fun _ hp => (mem_filter.mp hp).2)


#print axioms bjsStudy_product_relative
end ChenEffective
