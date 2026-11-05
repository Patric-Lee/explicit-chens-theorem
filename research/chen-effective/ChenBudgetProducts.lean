import ChenBudget
import OptimizedEulerProductPower

noncomputable section
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory SwitchingPrinciple
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- A quantitative product profile whose analytic feasibility is proved. -/
structure PrimeProductProfile where
  cutoff : ℝ
  error : ℝ
  cutoff_ten : 10 ≤ cutoff
  error_nonneg : 0 ≤ error
  error_cap : error ≤ 1/10000
  power_error : 130000000000000*cutoff^(-1/68 : ℝ) ≤ error/2

theorem budget_interval_product (P : PrimeProductProfile) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) (u z : ℝ) (hu : P.cutoff ≤ u) (huz : u ≤ z)
    (hinterval : ∀ p ∈ s, u ≤ (p : ℝ) ∧ (p : ℝ) < z) :
    (∏ p ∈ s, (1-1/((p : ℝ)-1))⁻¹) ≤ (1+P.error)*(log z/log u) := by
  have hu10 := P.cutoff_ten.trans hu
  have hU : 0 < P.cutoff := by linarith only [P.cutoff_ten]
  have he := (mul_le_mul_of_nonneg_left
    (rpow_le_rpow_of_nonpos hU hu (by norm_num : (-1/68 : ℝ) ≤ 0))
    (by norm_num : (0 : ℝ) ≤ 130000000000000)).trans P.power_error
  have hnonneg : 0 ≤ 130000000000000*u^(-1/68 : ℝ) := by positivity
  have hsmall : |130000000000000*u^(-1/68 : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg hnonneg]
    linarith only [he,P.error_cap]
  have hExp := Real.abs_exp_sub_one_le hsmall
  rw [abs_of_nonneg hnonneg] at hExp
  have hfactor : exp (130000000000000*u^(-1/68 : ℝ)) ≤ 1+P.error := by
    linarith only [(abs_le.mp hExp).2,he]
  have hratio : 0 ≤ log z/log u := by
    apply div_nonneg <;> apply log_nonneg <;> linarith only [hu10,huz]
  exact (optimized_goldbach_interval_power s hs u z hu10 huz hinterval).trans
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hfactor hratio)

theorem budget_presieved_product (P : PrimeProductProfile) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p)
    (hpresieve : ∀ p ∈ s, P.cutoff ≤ (p : ℝ))
    (u z : ℝ) (hu : 1 < u) (huz : u ≤ z)
    (hinterval : ∀ p ∈ s, u ≤ (p : ℝ) ∧ (p : ℝ) < z) :
    (∏ p ∈ s, (1-1/((p : ℝ)-1))⁻¹) ≤ (1+P.error)*(log z/log u) := by
  by_cases hUu : P.cutoff ≤ u
  · exact budget_interval_product P s hs u z hUu huz hinterval
  have huU : u ≤ P.cutoff := le_of_not_ge hUu
  have hlu : 0 < log u := log_pos hu
  have hlz : 0 < log z := log_pos (hu.trans_le huz)
  by_cases hzU : z ≤ P.cutoff
  · have hempty : s=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      linarith only [hpresieve p hp,(hinterval p hp).2,hzU]
    rw [hempty,Finset.prod_empty]
    have hr : 1 ≤ log z/log u := (le_div_iff₀ hlu).mpr
      (by simpa using log_le_log (by linarith only [hu] : 0 < u) huz)
    nlinarith only [hr,P.error_nonneg]
  have hUz : P.cutoff ≤ z := le_of_not_ge hzU
  apply (budget_interval_product P s hs P.cutoff z le_rfl hUz
    (fun p hp => ⟨hpresieve p hp,(hinterval p hp).2⟩)).trans
  apply mul_le_mul_of_nonneg_left _ (by linarith only [P.error_nonneg])
  exact div_le_div_of_nonneg_left hlz.le hlu (log_le_log (by linarith only [hu] : 0 < u) huU)

def optimizedProductProfile : PrimeProductProfile where
  cutoff := (3 : ℝ)^(2788 : ℝ)
  error := 1/100000
  cutoff_ten := by
    calc
      (10 : ℝ) ≤ 3^(3 : ℕ) := by norm_num
      _ = 3^(3 : ℝ) := (rpow_natCast _ _).symm
      _ ≤ _ := rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  error_nonneg := by norm_num
  error_cap := by norm_num
  power_error := by
    rw [← rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num [rpow_neg]

def budgetPresieveStart : ℝ := (3 : ℝ)^(2788 : ℝ)

theorem product_profile_relative (P : PrimeProductProfile) (S : BoundingSieve)
    (hodd : ∀ p ∈ S.prodPrimes.primeFactors, 2 < p)
    (hnu : ∀ p ∈ S.prodPrimes.primeFactors, S.nu p=1/((p : ℝ)-1)) :
    HasRelativeSieveProduct (preSieveCounting S P.cutoff) P.error := by
  intro u z hu huz
  unfold suzukiLocalRatio
  change (∏ p ∈ (restrictSievePrimes S P.cutoff).prodPrimes.primeFactors.filter
    (fun p : ℕ => u ≤ (p : ℝ) ∧ (p : ℝ) < z), (1-S.nu p)⁻¹) ≤ _
  rw [restrictSievePrimes_primeFactors]
  let s := (S.prodPrimes.primeFactors.filter (fun p : ℕ => P.cutoff ≤ (p : ℝ))).filter
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
  exact budget_presieved_product P s hs (fun _ hp => (mem_filter.mp (mem_filter.mp hp).1).2)
    u z hu huz (fun _ hp => (mem_filter.mp hp).2)

/-- Exact logarithmic-level coordinate. It avoids committing the interface
to an artificially tiny fixed power loss in N. -/
theorem budget_logarithmic_level_ratio (N : ℝ) (B Q : ℝ) (hN : 1 < N) (hQ : 0 < Q) :
    log ((N^(1/2 : ℝ)/(log N)^B)/(2*Q))/log (N^(1/10 : ℝ)) =
      5-10*(B*log (log N)+log (2*Q))/log N := by
  have hN0 : 0 < N := by linarith only [hN]
  have hL : 0 < log N := log_pos hN
  rw [log_div (div_pos (rpow_pos_of_pos hN0 _) (rpow_pos_of_pos hL _)).ne'
      (mul_pos (by norm_num) hQ).ne',
    log_div (rpow_pos_of_pos hN0 _).ne' (rpow_pos_of_pos hL _).ne',
    log_rpow hN0,log_rpow hL,log_rpow hN0]
  field_simp
  ring

#print axioms product_profile_relative
#print axioms budget_logarithmic_level_ratio
end ChenEffective
