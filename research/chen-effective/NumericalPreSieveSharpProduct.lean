import NumericalPreSieveCounting

namespace ChenEffective
open Real Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable def sharpPresieveStart : ℝ := (3 : ℝ) ^ (10240 : ℝ)
noncomputable def sharpPresieveError : ℝ := 1 / (10 : ℝ) ^ 20

theorem sharpPresieveStart_ten : 10 ≤ sharpPresieveStart := by
  calc
    (10 : ℝ) ≤ (3 : ℝ) ^ (3 : ℕ) := by norm_num
    _ = (3 : ℝ) ^ (3 : ℝ) := (rpow_natCast _ _).symm
    _ ≤ _ := rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num : (3 : ℝ) ≤ 10240)

theorem sharpPresieveStart_error {u : ℝ} (hu : sharpPresieveStart ≤ u) :
    130000000000000 * u ^ (-1 / 128 : ℝ) ≤ sharpPresieveError / 2 := by
  have hU : 0 < sharpPresieveStart := by unfold sharpPresieveStart; positivity
  have hh := rpow_le_rpow_of_nonpos hU hu (by norm_num : (-1 / 128 : ℝ) ≤ 0)
  have hid : sharpPresieveStart ^ (-1 / 128 : ℝ) = ((3 : ℝ) ^ (80 : ℕ))⁻¹ := by
    unfold sharpPresieveStart
    rw [← rpow_mul (by norm_num)]
    norm_num [rpow_neg]
  rw [hid] at hh
  have hb := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 130000000000000)
  exact hb.trans (by norm_num [sharpPresieveError])

theorem goldbach_interval_sharp_error (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) (u z : ℝ)
    (hu : sharpPresieveStart ≤ u) (huz : u ≤ z)
    (hinterval : ∀ p ∈ s, u ≤ (p : ℝ) ∧ (p : ℝ) < z) :
    (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
      (1 + sharpPresieveError) * (log z / log u) := by
  have hu10 := sharpPresieveStart_ten.trans hu
  have hu0 : 0 < u := by linarith
  have hl : 0 ≤ log z / log u := by
    apply div_nonneg <;> apply log_nonneg <;> linarith
  have hE := sharpPresieveStart_error hu
  have hEn : 0 ≤ 130000000000000 * u ^ (-1 / 128 : ℝ) := by positivity
  have he := Real.abs_exp_sub_one_le (show |130000000000000 * u ^ (-1 / 128 : ℝ)| ≤ 1 by
    rw [abs_of_nonneg hEn]; norm_num [sharpPresieveError] at hE; linarith)
  rw [abs_of_nonneg hEn] at he
  have he' : exp (130000000000000 * u ^ (-1 / 128 : ℝ)) ≤ 1 + sharpPresieveError := by
    have hh := (abs_le.mp he).2
    linarith
  exact (goldbach_interval_power s hs u z hu10 huz hinterval).trans (by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left he' hl)

theorem goldbach_presieved_sharp_error (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p)
    (hpresieve : ∀ p ∈ s, sharpPresieveStart ≤ (p : ℝ))
    (u z : ℝ) (hu : 1 < u) (huz : u ≤ z)
    (hinterval : ∀ p ∈ s, u ≤ (p : ℝ) ∧ (p : ℝ) < z) :
    (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
      (1 + sharpPresieveError) * (log z / log u) := by
  by_cases hUu : sharpPresieveStart ≤ u
  · exact goldbach_interval_sharp_error s hs u z hUu huz hinterval
  have huU : u ≤ sharpPresieveStart := le_of_not_ge hUu
  have hlu : 0 < log u := log_pos hu
  have hlz : 0 < log z := log_pos (hu.trans_le huz)
  by_cases hzU : z ≤ sharpPresieveStart
  · have hempty : s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      linarith [hpresieve p hp, (hinterval p hp).2]
    rw [hempty, prod_empty]
    have hr : 1 ≤ log z / log u := (le_div_iff₀ hlu).mpr (by
      simpa using log_le_log (by linarith : 0 < u) huz)
    have he : 0 ≤ sharpPresieveError := by norm_num [sharpPresieveError]
    nlinarith
  have hUz : sharpPresieveStart ≤ z := le_of_not_ge hzU
  have hb := goldbach_interval_sharp_error s hs sharpPresieveStart z le_rfl hUz
    (fun p hp => ⟨hpresieve p hp, (hinterval p hp).2⟩)
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num [sharpPresieveError])
  exact div_le_div_of_nonneg_left hlz.le hlu (log_le_log (by linarith : 0 < u) huU)

theorem preSieveCounting_goldbach_relative (S : BoundingSieve)
    (hodd : ∀ p ∈ S.prodPrimes.primeFactors, 2 < p)
    (hnu : ∀ p ∈ S.prodPrimes.primeFactors, S.nu p = 1 / ((p : ℝ) - 1)) :
    HasRelativeSieveProduct (preSieveCounting S sharpPresieveStart) sharpPresieveError := by
  intro u z hu huz
  unfold suzukiLocalRatio
  change (∏ p ∈ (restrictSievePrimes S sharpPresieveStart).prodPrimes.primeFactors.filter
    (fun p : ℕ => u ≤ (p : ℝ) ∧ (p : ℝ) < z), (1 - S.nu p)⁻¹) ≤ _
  rw [restrictSievePrimes_primeFactors]
  let s := (S.prodPrimes.primeFactors.filter (fun p : ℕ => sharpPresieveStart ≤ (p : ℝ))).filter
    (fun p : ℕ => u ≤ (p : ℝ) ∧ (p : ℝ) < z)
  have hs : ∀ p ∈ s, p.Prime ∧ 2 < p := by
    intro p hp
    have hP := (mem_filter.mp (mem_filter.mp hp).1).1
    exact ⟨Nat.prime_of_mem_primeFactors hP, hodd p hP⟩
  have hid : (∏ p ∈ s, (1 - S.nu p)⁻¹) = ∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
    apply prod_congr rfl
    intro p hp
    rw [hnu p (mem_filter.mp (mem_filter.mp hp).1).1]
  change (∏ p ∈ s, (1 - S.nu p)⁻¹) ≤ _
  rw [hid]
  exact goldbach_presieved_sharp_error s hs (fun _ hp => (mem_filter.mp (mem_filter.mp hp).1).2)
    u z hu huz (fun _ hp => (mem_filter.mp hp).2)

#print axioms preSieveCounting_goldbach_relative
end ChenEffective
