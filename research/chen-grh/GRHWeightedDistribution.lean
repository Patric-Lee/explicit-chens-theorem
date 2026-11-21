import GRHPrimeAPMaxima
import GRH14ErrorBudget
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDivisorMean

/-! A direct squarefree weighted distribution estimate at the H<14 target.
Only the elementary ordered-divisor mean is used from the existing Fouvry
prerequisite file; no Li--Liu analytic theorem is used. -/
namespace ChenEffective.GRH
open Real Finset
open MathlibNt.SieveTheory.BombieriVinogradov
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

private theorem divisor_weight_squarefree (n : ℕ) (hn : Squarefree n) :
    fouvryTau 3 n = 3^n.primeFactors.card := by
  rw [← (fouvryTau_multiplicative 3).prod_primeFactors hn]
  have hp (p : ℕ) (hpm : p ∈ n.primeFactors) : fouvryTau 3 p = 3 := by
    have hh := fouvryTau_prime_pow (Nat.prime_of_mem_primeFactors hpm) 3 1
    simpa [Nat.multichoose_eq] using hh
  simp_rw [Finset.prod_congr rfl hp]
  simp

theorem three_omega_mass (D : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 D)
    (hsq : ∀ d ∈ S, Squarefree d) :
    (∑ d ∈ S, (3:ℝ)^d.primeFactors.card) ≤ (D:ℝ)*(1+Real.log D)^2 := by
  have hh := sum_fouvryTau_le 2 D
  apply le_trans _ hh
  calc
    _ = ∑ d ∈ S, (fouvryTau 3 d:ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [divisor_weight_squarefree d (hsq d hd),Nat.cast_pow,Nat.cast_ofNat]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        have hh := Finset.mem_Icc.mp (hS hd)
        exact Finset.mem_Ioc.mpr ⟨by omega,hh.2⟩
      · intro d _ _
        positivity

theorem weighted_prefix_AP_numerical {N D : ℕ}
    (hL : (1000000:ℝ) ≤ Real.log N) (hD : 1 ≤ D)
    (hlevel : (D:ℝ) ≤ (N:ℝ)^(249/500:ℝ)) (S : Finset ℕ)
    (hS : S ⊆ Icc 1 D) (hsq : ∀ d ∈ S, Squarefree d) :
    (∑ d ∈ S, (3:ℝ)^d.primeFactors.card*standardPrimeAPPrefixMaxError N d) ≤
      (1e-12:ℝ)*N/(Real.log N)^2 := by
  let L := Real.log (N:ℝ)
  let Y := (N:ℝ)^(501/1000:ℝ)
  have hN2 : 2 ≤ N := by
    by_contra hn
    have hh : N ≤ 1 := by omega
    interval_cases N <;> norm_num at hL
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL0 : 0 < L := by dsimp only [L]; linarith only [hL]
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith only [hL]
  have hY0 : 0 ≤ Y := by dsimp only [Y]; positivity
  have hD0 : (0:ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hDN : (D:ℝ) ≤ N := hlevel.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1
      (show (249/500:ℝ) ≤ 1 by norm_num))
  have hlogD : Real.log (D:ℝ) ≤ L := Real.log_le_log hD0 hDN
  have hlogD0 : 0 ≤ Real.log (D:ℝ) := Real.log_nonneg (by exact_mod_cast hD)
  have hE (d : ℕ) (hd : d ∈ S) : standardPrimeAPPrefixMaxError N d ≤
      (8*10^16:ℝ)*L^3*Y := by
    obtain ⟨hd1,hdD⟩ := Finset.mem_Icc.mp (hS hd)
    have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hlogd : Real.log (d:ℝ) ≤ L :=
      Real.log_le_log hd0 ((by exact_mod_cast hdD : (d:ℝ)≤D).trans hDN)
    calc
      _ ≤ (10^16:ℝ)*(Real.log d+Real.log N)^3*(N:ℝ)^(501/1000:ℝ) :=
        prime_AP_max_numerical hN2 (by linarith only [hL]) (by omega)
      _ ≤ (10^16:ℝ)*(2*L)^3*Y := by gcongr; linarith only [hlogd]
      _ = _ := by ring
  have hsum : (∑ d ∈ S, (3:ℝ)^d.primeFactors.card*standardPrimeAPPrefixMaxError N d) ≤
      (8*10^16:ℝ)*L^3*Y*((D:ℝ)*(1+Real.log D)^2) := by
    calc
      _ ≤ ∑ d ∈ S, (3:ℝ)^d.primeFactors.card*((8*10^16:ℝ)*L^3*Y) := by
        apply Finset.sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left (hE d hd) (by positivity)
      _ = ((8*10^16:ℝ)*L^3*Y)*(∑ d ∈ S, (3:ℝ)^d.primeFactors.card) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro d _; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (three_omega_mass D S hS hsq) (by positivity)
  have hprod : Y*(N:ℝ)^(249/500:ℝ) = (N:ℝ)^(999/1000:ℝ) := by
    dsimp only [Y]
    rw [← Real.rpow_add hN0]
    congr 1
    norm_num
  have hmain : (∑ d ∈ S, (3:ℝ)^d.primeFactors.card*standardPrimeAPPrefixMaxError N d) ≤
      (320000000000000000:ℝ)*L^5*(N:ℝ)^(999/1000:ℝ) := by
    apply hsum.trans
    calc
      _ ≤ (8*10^16:ℝ)*L^3*Y*((N:ℝ)^(249/500:ℝ)*(2*L)^2) := by gcongr; linarith only [hlogD,hL1]
      _ = (320000000000000000:ℝ)*L^5*(Y*(N:ℝ)^(249/500:ℝ)) := by ring
      _ = _ := by rw [hprod]
  have hexp : (N:ℝ)^(999/1000:ℝ) = (N:ℝ)*Real.exp (-L/1000) := by
    rw [Real.rpow_def_of_pos hN0]
    change Real.exp (L*(999/1000:ℝ)) = _
    rw [show L*(999/1000:ℝ) = L+(-L/1000) by ring,Real.exp_add]
    rw [show Real.exp L = (N:ℝ) from Real.exp_log hN0]
  have hpayBig := GRH14.distribution_error_payment hL (C := (320000000000000000000000:ℝ))
    (by norm_num) (α := 1/1000) le_rfl (k := 7) (by norm_num)
  have hpay : (320000000000000000:ℝ)*L^7*Real.exp (-(1/1000:ℝ)*L) ≤ (1e-12:ℝ) := by
    have heq : (320000000000000000000000:ℝ)*L^7*Real.exp (-(1/1000:ℝ)*L) =
        (1000000:ℝ)*((320000000000000000:ℝ)*L^7*Real.exp (-(1/1000:ℝ)*L)) := by ring
    rw [heq] at hpayBig
    nlinarith only [hpayBig]
  have hid : (320000000000000000:ℝ)*L^5*(N:ℝ)^(999/1000:ℝ) =
      ((320000000000000000:ℝ)*L^7*Real.exp (-(1/1000:ℝ)*L))*((N:ℝ)/L^2) := by
    rw [hexp,show -(1/1000:ℝ)*L = -L/1000 by ring]
    field_simp [hL0.ne']
  calc
    _ ≤ (320000000000000000:ℝ)*L^5*(N:ℝ)^(999/1000:ℝ) := hmain
    _ = _ := hid
    _ ≤ (1e-12:ℝ)*((N:ℝ)/L^2) :=
      mul_le_mul_of_nonneg_right hpay (by positivity)
    _ = _ := by ring

theorem weighted_AP_numerical {N D : ℕ}
    (hN : GRH14.targetCutoff ≤ N) (hD : 1 ≤ D)
    (hlevel : (D:ℝ) ≤ (N:ℝ)^(249/500:ℝ)) (S : Finset ℕ)
    (hS : S ⊆ Icc 1 D) (hsq : ∀ d ∈ S, Squarefree d) :
    (∑ d ∈ S, (3:ℝ)^d.primeFactors.card*standardPrimeAPMaxError N d) ≤
      (1e-12:ℝ)*N/(Real.log N)^2 := by
  apply le_trans _ (weighted_prefix_AP_numerical (GRH14.target_log_lower hN) hD hlevel S hS hsq)
  apply Finset.sum_le_sum
  intro d _
  exact mul_le_mul_of_nonneg_left (standardPrimeAPMaxError_le_prefixMaxError N d) (by positivity)

#print axioms three_omega_mass
#print axioms weighted_AP_numerical
end ChenEffective.GRH
