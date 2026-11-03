import NumericalSelbergDenominatorClosed
import MathlibNt.SieveTheory.Liu.PrimePairs.LiuPrimePairLogGridLimit

noncomputable section
namespace ChenEffective
open MathlibNt.SieveTheory
open LiuWeight
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
attribute [local irreducible] logPowerCutoff mertensProductThreshold

private opaque primePairPowerExponentCertificate : {k : ℕ // k=10^80} := ⟨10^80,rfl⟩
def primePairPowerExponent : ℕ := primePairPowerExponentCertificate.1
theorem primePairPowerExponent_eq : primePairPowerExponent=10^80 := primePairPowerExponentCertificate.2
@[irreducible] def primePairThreshold : ℕ := max (selbergMertensEndpoint^10) (3^primePairPowerExponent)

theorem numerical_prime_pair_parameters {N : ℕ} (hN : primePairThreshold ≤ N) :
    9 ≤ N ∧ (10^80 : ℝ) ≤ Real.log (N : ℝ) ∧
      (principalNumericalThreshold 1 : ℝ) ≤ (N : ℝ)^(1/10 : ℝ) ∧
      (logPowerCutoff 2 : ℝ) ≤ (N : ℝ)^(1/10 : ℝ) := by
  have hn := hN
  unfold primePairThreshold at hn
  obtain ⟨hM,hP⟩ := max_le_iff.mp hn
  have hlog := log_ge_power_three hP
  rw [primePairPowerExponent_eq] at hlog
  norm_num only [Nat.cast_pow,Nat.cast_ofNat] at hlog
  have hlogR : (10^80 : ℝ) ≤ Real.log (N : ℝ) := by
    norm_num at hlog ⊢
    exact hlog
  have hNpos : 0 < N := by
    by_contra hh
    have he : N=0 := by omega
    subst N
    norm_num at hlog
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hln := Real.log_le_sub_one_of_pos hN0
  have hN9 : 9 ≤ N := by exact_mod_cast (by linarith only [hlog,hln] : (9 : ℝ) ≤ N)
  have hroot : (selbergMertensEndpoint : ℝ) ≤ (N : ℝ)^(1/10 : ℝ) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg _) hN0.le (by norm_num : (0 : ℝ) < 10)).mpr
    exact_mod_cast hM
  have hPM : principalNumericalThreshold 1 ≤ selbergMertensEndpoint := by
    rw [selbergMertensEndpoint_eq]
    unfold mertensProductThreshold
    exact le_max_left _ _
  have h2P : logPowerCutoff 2 ≤ principalNumericalThreshold 1 := by
    unfold principalNumericalThreshold logPowerCutoff
    apply Nat.pow_le_pow_right (by norm_num)
    norm_num
  have hPMR : (principalNumericalThreshold 1 : ℝ) ≤ selbergMertensEndpoint := by exact_mod_cast hPM
  have h2PR : (logPowerCutoff 2 : ℝ) ≤ principalNumericalThreshold 1 := by exact_mod_cast h2P
  exact ⟨hN9,hlogR,hPMR.trans hroot,h2PR.trans (hPMR.trans hroot)⟩

private opaque primePairGridCertificate : {n : ℕ // n=1000000000000} := ⟨1000000000000,rfl⟩
def primePairGrid : ℕ := primePairGridCertificate.1
theorem primePairGrid_eq : primePairGrid=1000000000000 := primePairGridCertificate.2
theorem primePairGrid_pos : 0 < primePairGrid := by rw [primePairGrid_eq]; norm_num

#print axioms numerical_prime_pair_parameters
end ChenEffective
