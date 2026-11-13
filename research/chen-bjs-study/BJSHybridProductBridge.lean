import BJSStudyProducts
import BJSHybridPrimePowers
import NumericalGoldbachInterval
import DusartPort.Application

namespace ChenEffective.HybridProduct
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

/-- The remaining finite-window analytic obligation. This is a proposition,
not an axiom, and is not asserted by this module. The infinite tail is
discharged below by the existing proved Dusart branch. -/
def HybridPrefixWindow : Prop :=
  ∀ x : ℝ, 4000000 ≤ x → x ≤ (3:ℝ)^120 →
    |primeReciprocalSum ⌊x⌋₊-(log (log x)+mertensSecondConstant)| ≤ 1/9000

theorem hybrid_prefix_of_window (hwindow : HybridPrefixWindow)
    {x : ℝ} (hx : 4000000 ≤ x) :
    |primeReciprocalSum ⌊x⌋₊-(log (log x)+mertensSecondConstant)| ≤ 1/9000 := by
  by_cases hsmall : x ≤ (3:ℝ)^120
  · exact hwindow x hx hsmall
  have hbig : (3:ℝ)^120 ≤ x := le_of_not_ge hsmall
  have hlog := log_le_log (by positivity : (0:ℝ) < 3^120) hbig
  rw [log_pow] at hlog
  have hL : (120:ℝ) ≤ log x := by
    norm_num only [Nat.cast_ofNat] at hlog
    nlinarith only [hlog,one_le_log_three]
  apply (dusart_sharp_mertens hbig).trans
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*(log x)^2)).mpr
  nlinarith only [hL,sq_nonneg (log x-120)]

theorem hybrid_reciprocal_interval (hwindow : HybridPrefixWindow)
    (s : Finset ℕ) (u z : ℝ) (hu : 4000000 ≤ u) (huz : u ≤ z)
    (hs : ∀ p ∈ s, p.Prime ∧ u ≤ (p:ℝ) ∧ (p:ℝ) ≤ z) :
    (∑ p ∈ s, 1/(p:ℝ)) ≤ log (log z/log u)+2/9000 := by
  have hu1 : 1 < u := by linarith only [hu]
  have hlu : 0 < log u := log_pos hu1
  have hlz : 0 < log z := log_pos (hu1.trans_le huz)
  have hupper := (abs_le.mp (hybrid_prefix_of_window hwindow (hu.trans huz))).2
  have hdiff : (∑ p ∈ s, 1/(p:ℝ)) ≤
      (log (log z)+mertensSecondConstant+1/9000)-
        (log (log u)+mertensSecondConstant-1/9000) := by
    rcases lt_or_eq_of_le hu with hstrict | heq
    · apply bjsStudy_interval_of_prefix s (by norm_num : (0:ℝ) ≤ 4000000)
        hstrict huz hs
        (fun x hx => by have hh := (abs_le.mp (hybrid_prefix_of_window hwindow hx.le)).1; linarith only [hh])
        (by linarith only [hupper])
      fun_prop (disch := positivity)
    · have hd := bjsStudy_interval_prefix_composite s 4000000 z
        (by norm_num) (by norm_num; linarith only [heq,huz])
        (by intro p hp; refine ⟨(hs p hp).1,?_,(hs p hp).2.2⟩; change (4000000:ℝ) ≤ (p:ℝ); rw [heq]; exact (hs p hp).2.1)
      have hlo := (abs_le.mp (hybrid_prefix_of_window hwindow hu)).1
      have hfloor : ⌊u⌋₊=4000000 := by rw [← heq]; norm_num
      rw [hfloor] at hlo
      linarith only [hd,hlo,hupper]
  rw [log_div hlz.ne' hlu.ne']
  linarith only [hdiff]

/-- The exact product profile needed by the sharp density theorem follows
from the finite-window obligation, with the endpoint and Goldbach local
factor corrections included. No product assumption is silently supplied. -/
theorem hybrid_interval_product (hwindow : HybridPrefixWindow)
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) (u z : ℝ)
    (hu : 4000000 ≤ u) (huz : u ≤ z)
    (hinterval : ∀ p ∈ s, u ≤ (p:ℝ) ∧ (p:ℝ) < z) :
    (∏ p ∈ s, (1-1/((p:ℝ)-1))⁻¹) ≤ (1+(1/4000:ℝ))*(log z/log u) := by
  have hu1 : 1 < u := by linarith only [hu]
  have hlu : 0 < log u := log_pos hu1
  have hlz : 0 < log z := log_pos (hu1.trans_le huz)
  have hr := hybrid_reciprocal_interval hwindow s u z hu huz
    (fun p hp => ⟨(hs p hp).1,(hinterval p hp).1,(hinterval p hp).2.le⟩)
  let k : ℕ := 3999999
  let n : ℕ := s.sup id
  have hk : ∀ p ∈ s, k < p := by
    intro p hp
    have hpge : 4000000 ≤ p := by exact_mod_cast hu.trans (hinterval p hp).1
    dsimp [k]
    omega
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
  have herr : (2/9000:ℝ)+12*(2/(k:ℝ)) ≤ (2/9000+24/3999999) := by norm_num [k]
  have hprod : 0 < ∏ p ∈ s, (1-1/((p:ℝ)-1))⁻¹ :=
    Finset.prod_pos (fun p hp => inv_pos.mpr (goldbach_local_factor_pos (hs p hp).2))
  have hlprod : log (∏ p ∈ s, (1-1/((p:ℝ)-1))⁻¹) ≤
      log (log z/log u)+((2/9000+24/3999999):ℝ) := by
    rw [Real.log_prod (fun p hp => (inv_pos.mpr (goldbach_local_factor_pos (hs p hp).2)).ne')]
    have hh := Finset.sum_le_sum (s:=s)
      (fun p hp => log_goldbach_inverse_factor_le (hs p hp).1 (hs p hp).2)
    simp only [Finset.sum_add_distrib,div_eq_mul_inv,← Finset.mul_sum] at hh
    have ht := mul_le_mul_of_nonneg_left hsq (by norm_num : (0:ℝ) ≤ 12)
    simp only [div_eq_mul_inv,← Finset.mul_sum] at ht hr
    simp only [div_eq_mul_inv,one_mul] at hh ht hr herr ⊢
    linarith only [hh,ht,hr,herr]
  have hh := exp_le_exp.mpr hlprod
  rw [exp_log hprod,exp_add,exp_log (div_pos hlz hlu)] at hh
  apply hh.trans
  calc
    _ ≤ (log z/log u)*(1+1/4000) :=
      mul_le_mul_of_nonneg_left hybrid_product_payment (div_pos hlz hlu).le
    _ = _ := mul_comm _ _
#print axioms hybrid_interval_product
end ChenEffective.HybridProduct






