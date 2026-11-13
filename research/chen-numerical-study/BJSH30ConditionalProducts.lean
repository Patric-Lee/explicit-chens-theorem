import BJSHybridProductBridge

noncomputable section
namespace ChenEffective.H30Conditional
open Real Finset
open MathlibNt.SieveTheory.SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- TEMPORARY numerical-study input, backed by the JavaScript hybrid pilot.
This includes the analytic extension above the finite prime scan; it is not
claimed to be a kernel-checked finite certificate. See NUMERICAL_H30.md. -/
axiom temporary_reciprocal_prefix_window : HybridProduct.HybridPrefixWindow

noncomputable def bjsStudyPresieveStart : ℝ := 4000000

theorem bjsStudy_interval_product (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) (u z : ℝ)
    (hu : bjsStudyPresieveStart ≤ u) (huz : u ≤ z)
    (hinterval : ∀ p ∈ s, u ≤ (p : ℝ) ∧ (p : ℝ) < z) :
    (∏ p ∈ s, (1-1/((p : ℝ)-1))⁻¹) ≤ (1+(1/4000:ℝ))*(log z/log u) :=
  HybridProduct.hybrid_interval_product temporary_reciprocal_prefix_window s hs u z hu huz hinterval

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
end ChenEffective.H30Conditional
