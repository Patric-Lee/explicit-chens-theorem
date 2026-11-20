import BJSH29Analytic
import BJSH30Budget

/- Derived from BJSH30DistributionGeometry; checked as new H29 proof source. -/
section

noncomputable section
namespace ChenEffective.H29
open ChenEffective.H30
open Real
open MathlibNt.SieveTheory LiuWeight
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem log_ten_cap : log (10:ℝ)≤12/5 := by
  have he : (27/10:ℝ)≤exp 1 := by linarith only [exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤27/10) he 12
  rw [← exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat,mul_one] at hp
  have hn : (10:ℝ)^5≤exp 12 := (by norm_num : (10:ℝ)^5≤150094635296999121/1000000000000).trans hp
  have hl := log_le_log (by positivity : (0:ℝ)<10^5) hn
  rw [log_pow,log_exp] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [hl]

theorem log_linear_budget {L : ℝ} (hL : (3*10^12:ℝ)≤L) :
    (10^11:ℝ)*log L≤L := by
  have hLp : 0<L := lt_of_lt_of_le (by norm_num) hL
  have hh := log_le_sub_one_of_pos (div_pos hLp (by norm_num : (0:ℝ)<3*10^12))
  rw [log_div hLp.ne' (by norm_num)] at hh
  have hbase : log (3*10^12:ℝ)≤30 := by
    rw [log_mul (by norm_num) (by norm_num),log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [log_ten_cap,log_three_cap]
  norm_num at hh hbase hL ⊢
  nlinarith only [hh,hbase,hL]

theorem source_modulus_of_log (B m N : ℕ) (hm : 0 < m)
    (hL : ((3*10^12):ℝ)≤log (N:ℝ)) (hBudget : m*B≤10^11) :
    liuSourceDEpsilon N (1/(m:ℝ)) ≤ panModulusCutoff N (B:ℝ) := by
  have hn9 := (H30.numerical_prime_pair_parameters (show (10^12:ℝ)≤log (N:ℝ) by linarith only [hL])).1
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hlogL : 0≤log (log (N:ℝ)) := log_nonneg (by linarith only [hL])
  have hb : ((m:ℝ)*B)*log (log (N:ℝ))≤log (N:ℝ) := by
    have hc : (m:ℝ)*B≤10^11 := by exact_mod_cast hBudget
    exact (mul_le_mul_of_nonneg_right hc hlogL).trans (log_linear_budget hL)
  have hpow : log (N:ℝ)^B≤(N:ℝ)^(1/(m:ℝ)) := by
    apply (log_le_log_iff (pow_pos hl _) (rpow_pos_of_pos hn _)).mp
    rw [log_pow,log_rpow hn]
    have he : (1/(m:ℝ))*log (N:ℝ)=log (N:ℝ)/(m:ℝ) := by ring
    rw [he]
    apply (le_div_iff₀ hmR).mpr
    nlinarith only [hb]
  unfold liuSourceDEpsilon panModulusCutoff
  apply Nat.floor_mono
  rw [rpow_sub hn,rpow_natCast]
  exact div_le_div_of_nonneg_left (rpow_nonneg hn.le _) (pow_pos hl _) hpow

private opaque distributionCertificate : {n : ℕ // n=(3*10^12)} := ⟨(3*10^12),rfl⟩
def distributionExponent : ℕ := distributionCertificate.1
theorem distributionExponent_eq : distributionExponent=(3*10^12) := distributionCertificate.2
@[irreducible] def distributionThreshold : ℕ := 3^distributionExponent

theorem distribution_log {N : ℕ} (hN : distributionThreshold≤N) : ((3*10^12):ℝ)≤log (N:ℝ) := by
  unfold distributionThreshold at hN
  have hh := log_ge_power_three hN
  rw [distributionExponent_eq] at hh
  simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hh

theorem distribution_bv_cap {A : ℕ} (hA : A≤30) : numericalBVThreshold A≤distributionThreshold := by
  rw [numerical_BV_threshold_closed]
  unfold distributionThreshold
  apply Nat.pow_le_pow_right (by decide)
  rw [distributionExponent_eq]
  calc
    _ ≤ 16*(384*30+13569)^2 := by gcongr
    _ ≤ _ := by norm_num

#print axioms source_modulus_of_log
end ChenEffective.H29

end
end

/- Derived from BJSH30WeightedDistribution; checked as new H29 proof source. -/
section

namespace ChenEffective.H29
open ChenEffective.H30
open Finset Real
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.Richert1969
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem numerical_combined_squarefree {N d : ℕ} {ε : ℝ}
    (hd : d ∈ chenReducedCombinedModuli N ε) : Squarefree d := by
  rcases Finset.mem_biUnion.mp hd with ⟨q, hq, hmImage⟩
  rcases Finset.mem_image.mp hmImage with ⟨r, hr, rfl⟩
  have hqSource := (Finset.mem_filter.mp hq).1
  have hqPrime := (Finset.mem_filter.mp hqSource).2.1
  have hrDiv : r ∣ jurkatRichertSourceSiftingProduct N :=
    Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hr).1
  have hrSquarefree := (jurkatRichertSourceSiftingProduct_squarefree N).squarefree_of_dvd hrDiv
  have hcop := jurkatRichertSourceMediumPrime_coprime_siftingDivisor hqSource hrDiv
  exact (Nat.squarefree_mul hcop).mpr ⟨hqPrime.squarefree, hrSquarefree⟩

def weightedSaving (A : ℕ) : ℕ := 2 * A + 18
def weightedNumericalConstant (A : ℕ) : ℝ :=
  3145728 * (numericalBVConstant (weightedSaving A) + 1)
def weightedNumericalThreshold (A m : ℕ) : ℕ :=
  max (numericalBVThreshold (weightedSaving A))
    (logPowerCutoff (m * highBVExponent (weightedSaving A)))

theorem weighted_distribution_of_log (A m N : ℕ) (hm : 0 < m)
    (hL : ((3*10^12):ℝ)≤Real.log (N:ℝ)) (hBV : numericalBVThreshold (weightedSaving A)≤N) (hBudget : m*highBVExponent (weightedSaving A)≤10^11) :
    jurkatRichertSourceReducedWeightedBVSum N (1 / (m : ℝ)) ≤
      weightedNumericalConstant A * (N : ℝ) / Real.log N ^ A := by
  let U := weightedSaving A
  let Q := LiuWeight.panModulusCutoff N (highBVExponent U : ℝ)
  let S := chenReducedCombinedModuli N (1 / (m : ℝ))
  let E := BombieriVinogradov.standardPrimeAPMaxError N
  let K := numericalBVConstant U
  have hBVcut : numericalBVThreshold U≤N := hBV
  have hN9 : 9≤N := (H30.numerical_prime_pair_parameters (show (10^12:ℝ)≤Real.log (N:ℝ) by linarith only [hL])).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
      (show (3 : ℝ) ≤ N by exact_mod_cast (show 3 ≤ N by omega))
    linarith only [hh, one_le_log_three]
  have hl : 0 < Real.log (N : ℝ) := by linarith only [hlog]
  have hK : 0 ≤ K := by
    dsimp [K, numericalBVConstant, bvConstant, primitiveNumericalConstant, principalNumericalConstant]
    positivity
  have hcut := source_modulus_of_log (highBVExponent U) m N hm hL hBudget
  have hQN : Q ≤ N := panModulusCutoff_le_endpoint N (highBVExponent U : ℝ)
    (by omega) (by positivity)
  have hS : S ⊆ Finset.Icc 1 Q := by
    intro d hd
    have hs := numerical_combined_squarefree hd
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hs.ne_zero,
      (chenReducedCombinedModuli_le_liuSourceDEpsilon hd).trans hcut⟩
  have hSN : S ⊆ Finset.Icc 1 N := hS.trans (Finset.Icc_subset_Icc_right hQN)
  have hE : ∀ d ∈ S, 0 ≤ E d := fun d _ => BombieriVinogradov.standardPrimeAPMaxError_nonneg N d
  have hsum : (∑ d ∈ S, E d) ≤ K * (N : ℝ) / Real.log N ^ U := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 Q, E d := Finset.sum_le_sum_of_subset_of_nonneg hS (fun d _ _ =>
        BombieriVinogradov.standardPrimeAPMaxError_nonneg N d)
      _ ≤ ∑ d ∈ Finset.Icc 1 Q, BombieriVinogradov.standardPrimeAPPrefixMaxError N d :=
        BombieriVinogradov.sum_standardPrimeAPMaxError_le_prefixMaxError N _
      _ ≤ _ := numerical_BV U N hBVcut
  have hmoment := numerical_totient_nine_mass (by omega : 1 ≤ N) S
    hSN (fun d hd => numerical_combined_squarefree hd)
  have hc := numerical_totient_cauchy S (fun d => (3 : ℝ) ^ d.primeFactors.card) E (12 * N)
    (fun d hd => (Finset.mem_Icc.mp (hSN hd)).1) hE
    (fun d hd => numerical_totient_standard_error hN9 (Finset.mem_Icc.mp (hSN hd)).1
      (Finset.mem_Icc.mp (hSN hd)).2)
  have heq : (∑ d ∈ S, ((3 : ℝ) ^ d.primeFactors.card) ^ 2 / d.totient) =
      ∑ d ∈ S, (9 : ℝ) ^ d.primeFactors.card / d.totient := by
    apply Finset.sum_congr rfl
    intro d _
    rw [pow_two, ← mul_pow]
    norm_num
  rw [heq] at hc
  have hm0 : 0 ≤ ∑ d ∈ S, (9 : ℝ) ^ d.primeFactors.card / d.totient :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hs0 : 0 ≤ ∑ d ∈ S, E d := Finset.sum_nonneg hE
  have hbig : threeOmegaErrorMass S E ^ 2 ≤
      (1 + Real.log N) ^ (18 : ℕ) * (12 * N * (K * N / Real.log N ^ U)) := by
    exact hc.trans (mul_le_mul hmoment
      (mul_le_mul_of_nonneg_left hsum (by positivity)) (by positivity)
      (by positivity))
  have hw0 : 0 ≤ jurkatRichertSourceReducedWeightedBVSum N (1 / (m : ℝ)) := by
    unfold jurkatRichertSourceReducedWeightedBVSum
    exact Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun d _ => by
      exact mul_nonneg (pow_nonneg (by norm_num) _)
        (BombieriVinogradov.standardPrimeAPMaxError_nonneg N (q * d))
  have ht0 : 0 ≤ threeOmegaErrorMass S E := Finset.sum_nonneg fun d hd =>
    mul_nonneg (pow_nonneg (by norm_num) _) (hE d hd)
  have hwsq := (sq_le_sq₀ hw0 ht0).2 (chenReducedWeightedBVSum_le_combinedMass N (1 / (m : ℝ)))
  have hlogbound : (1 + Real.log N) ^ (18 : ℕ) ≤ (2 * Real.log N) ^ (18 : ℕ) := by
    gcongr
    linarith only [hlog]
  have hsquare : jurkatRichertSourceReducedWeightedBVSum N (1 / (m : ℝ)) ^ 2 ≤
      (3145728 * K) * ((N : ℝ) / Real.log N ^ A) ^ 2 := by
    apply hwsq.trans (hbig.trans _)
    calc
      _ ≤ (2 * Real.log N) ^ (18 : ℕ) * (12 * N * (K * N / Real.log N ^ U)) :=
        mul_le_mul_of_nonneg_right hlogbound (by positivity)
      _ = _ := by
        dsimp [U, weightedSaving]
        rw [pow_add, pow_mul]
        field_simp
        ring
  have hC : 1 ≤ weightedNumericalConstant A := by
    change 1 ≤ 3145728 * (K + 1)
    linarith only [hK]
  have hCbig : 3145728 * K ≤ weightedNumericalConstant A ^ 2 := by
    have hh : 3145728 * K ≤ weightedNumericalConstant A := by
      change 3145728 * K ≤ 3145728 * (K + 1)
      linarith
    nlinarith only [hh, hC, sq_nonneg (weightedNumericalConstant A - 1)]
  have hp := mul_le_mul_of_nonneg_right hCbig (sq_nonneg ((N : ℝ) / Real.log N ^ A))
  have hh := hsquare.trans hp
  have hC0 : 0 ≤ weightedNumericalConstant A * (N : ℝ) / Real.log N ^ A := by
    apply div_nonneg (mul_nonneg (by linarith only [hC]) hN0.le) (pow_nonneg hl.le _)
  apply (sq_le_sq₀ hw0 hC0).mp
  convert hh using 1
  ring

#print axioms weighted_distribution_of_log
end ChenEffective.H29

end

/- Derived from BJSH30Distribution; checked as new H29 proof source. -/
section

noncomputable section
namespace ChenEffective.H29
open ChenEffective.H30
open Real Finset
open MathlibNt.SieveTheory SwitchingPrinciple LiuWeight
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem distribution_log_cutoff {k : ℕ} (hk : 16*(k+1)^2≤(3*10^12)) :
    logPowerCutoff k≤ distributionThreshold := by
  unfold distributionThreshold
  apply numerical_log_cutoff_cap
  rw [distributionExponent_eq]
  exact hk

theorem distribution_parameters {N : ℕ} (hN : distributionThreshold≤ N) :
    9≤ N ∧ 0< log (N:ℝ) ∧ logPowerCutoff 100≤ N := by
  have hcut := (distribution_log_cutoff (by norm_num : 16*((100:ℕ)+1)^2≤(3*10^12))).trans hN
  have hn9 := (logPowerCutoff_nine_le _).trans hcut
  exact ⟨hn9,log_pos (by exact_mod_cast (show 1< N by omega)),hcut⟩

theorem base_bv_order_three {N : ℕ} (hN : distributionThreshold≤ N) :
    (∑ q∈Icc 1 (panModulusCutoff N (highBVExponent 10:ℝ)),
      BombieriVinogradov.standardPrimeAPPrefixMaxError N q)≤(N:ℝ)/log (N:ℝ)^3 := by
  have hL := distribution_log hN
  have hl := (distribution_parameters hN).2.1
  have hb := numerical_BV 10 N ((distribution_bv_cap (by decide : 10≤30)).trans hN)
  have hc : numericalBVConstant 10≤ log (N:ℝ)^7 := by
    have hh : numericalBVConstant 10≤(2*10^18:ℝ) := by
      norm_num [numericalBVConstant,bvConstant,primitiveNumericalConstant,principalNumericalConstant,highBVConductorExponent]
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤(3*10^12)) hL 7
    nlinarith only [hh,hp]
  apply hb.trans
  calc
    _ ≤ log (N:ℝ)^7*N/log (N:ℝ)^10 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg N)) (pow_nonneg hl.le _)
    _ = _ := by field_simp

theorem weighted_distribution_paid (m N : ℕ) (hm : 0 < m)
    (hN : distributionThreshold≤ N) (hBudget : m*highBVExponent (weightedSaving 6)≤10^11) :
    jurkatRichertSourceReducedWeightedBVSum N (1/(m:ℝ))≤
      (1/10^8:ℝ)*(N:ℝ)/log (N:ℝ)^2 := by
  have hL := distribution_log hN
  have hl := (distribution_parameters hN).2.1
  have hb := weighted_distribution_of_log 6 m N hm hL
    ((distribution_bv_cap (by norm_num [weightedSaving] : weightedSaving 6≤30)).trans hN) hBudget
  have hc : weightedNumericalConstant 6≤(1/10^8:ℝ)*log (N:ℝ)^4 := by
    have hh : weightedNumericalConstant 6≤(10^26:ℝ) := by
      norm_num [weightedNumericalConstant,weightedSaving,numericalBVConstant,bvConstant,
        primitiveNumericalConstant,principalNumericalConstant,highBVConductorExponent]
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤(3*10^12)) hL 4
    nlinarith only [hh,hp]
  apply hb.trans
  calc
    _ ≤ ((1/10^8:ℝ)*log (N:ℝ)^4)*N/log (N:ℝ)^6 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg N)) (pow_nonneg hl.le _)
    _ = _ := by field_simp

theorem varying_distribution_paid (m d N : ℕ) (hm : 0 < m) (hd : 0< d) (hdcap : d≤10^7)
    (hN : distributionThreshold≤ N) (hBudget : m*highBVExponent (weightedSaving 6)≤10^11)
    (hEven : Even N) :
    jurkatRichertSourceVaryingQRemainderSum N (1/(m:ℝ))≤
      (1/(d:ℝ))*SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2 := by
  have hw := weighted_distribution_paid m N hm hN hBudget
  obtain ⟨hN9,hl,hcut⟩ := distribution_parameters hN
  have hL := distribution_log hN
  have hN0 : (0:ℝ)< N := by exact_mod_cast (show 0< N by omega)
  have hp := log_pow_le_rpow_inv_explicit (k:=10) (m:=10) (by norm_num) (by norm_num) hcut
  have hc := numerical_varying_correction hN9 (show (0:ℝ)≤1/(m:ℝ) by positivity)
  have hc' : jurkatRichertSourceVaryingQUnconditionalCorrection N (1/(m:ℝ))≤
      3000*N/log (N:ℝ)^3 := by
    apply hc.trans
    apply (le_div_iff₀ (pow_pos hl 3)).mpr
    have he : (N:ℝ)^(9/10:ℝ)*(N:ℝ)^(1/10:ℝ)=N := by rw [← rpow_add hN0]; norm_num
    have hh := mul_le_mul_of_nonneg_left hp (show 0≤3000*(N:ℝ)^(9/10:ℝ) by positivity)
    norm_num only [Nat.cast_ofNat] at hh
    have he' : 3000*(N:ℝ)^(9/10:ℝ)*(N:ℝ)^(1/10:ℝ)=3000*N := by rw [mul_assoc,he]
    have ht : log (N:ℝ)^7*log (N:ℝ)^3=log (N:ℝ)^10 := by ring
    nlinarith only [hh,he',congrArg (fun x : ℝ => 3000*(N:ℝ)^(9/10:ℝ)*x) ht]
  have hpay : 3000*N/log (N:ℝ)^3≤(1/10^8:ℝ)*N/log (N:ℝ)^2 := by
    apply (div_le_div_iff₀ (pow_pos hl 3) (pow_pos hl 2)).mpr
    have hh := mul_le_mul_of_nonneg_right (show (3000:ℝ)≤(1/10^8:ℝ)*log (N:ℝ) by linarith only [hL])
      (show 0≤(N:ℝ)*log (N:ℝ)^2 by positivity)
    nlinarith only [hh]
  have hf := jurkatRichertSourceVaryingQRemainderSum_le_weightedBV_add_correction N (1/(m:ℝ)) hEven (by omega)
  have hdR : (0:ℝ)< d := by exact_mod_cast hd
  have hdc : (d:ℝ)≤10^7 := by exact_mod_cast hdcap
  have hs := half_le_liuSingularSeries N
  have hcoef : (2/10^8:ℝ)≤(1/(d:ℝ))*SingularSeries.liuSingularSeries N := by
    rw [one_div,mul_comm,← div_eq_mul_inv]
    apply (le_div_iff₀ hdR).mpr
    linarith only [hs,hdc]
  have hmain := mul_le_mul_of_nonneg_right hcoef (show 0≤(N:ℝ)/log (N:ℝ)^2 by positivity)
  simp only [mul_div_assoc,mul_assoc] at hmain hw hpay hf hc' ⊢
  linarith only [hf,hw,hc',hpay,hmain]

#print axioms varying_distribution_paid
end ChenEffective.H29

end
end

/- Derived from BJSH30BaseDistribution; checked as new H29 proof source. -/
section

noncomputable section
namespace ChenEffective.H29
open ChenEffective.H30
open Real Finset
open MathlibNt.SieveTheory SwitchingPrinciple SingularSeries LiuWeight
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem base_distribution_paid (m d N : ℕ) (hm : 3≤ m) (hd : 0< d) (hdcap : d≤20000000)
    (hN : distributionThreshold≤ N) (hBudget : m*highBVExponent 10≤10^11) (hEven : Even N) :
    jurkatRichertSourceRemainderSum N (1/(m:ℝ))≤
      (1/(d:ℝ))*liuSingularSeries N*N/log (N:ℝ)^2 := by
  let b : ℕ := 1
  let C : ℝ := 1
  have hC : C≤ b := by norm_num [C,b]
  have hGlobal := distribution_log hN
  have hN9 := (distribution_parameters hN).1
  have hfour : logPowerCutoff 4≤ N := (distribution_log_cutoff (by norm_num : 16*((4:ℕ)+1)^2≤(3*10^12))).trans hN
  have hL : 4*(b:ℝ)*d+16*(d:ℝ)+1≤ log (N:ℝ) := by
    have hdRcap : (d:ℝ)≤20000000 := by exact_mod_cast hdcap
    dsimp only [b]
    norm_num only [Nat.cast_one]
    linarith only [hGlobal,hdRcap]
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hmR : (0:ℝ) < m := by exact_mod_cast (show 0< m by omega)
  have heps : 0<1/(m:ℝ) := one_div_pos.mpr hmR
  have hepsHalf : 1/(m:ℝ)<1/2 := by
    apply (div_lt_div_iff₀ hmR (by norm_num : (0:ℝ)<2)).mpr
    have hm3 : (3:ℝ)≤ m := by exact_mod_cast hm
    linarith only [hm3]
  have hlog := (distribution_parameters hN).2.1
  have hN0 : (0:ℝ)< N := by exact_mod_cast (show 0< N by omega)
  have hcut : liuSourceDEpsilon N (1/(m:ℝ))≤ panModulusCutoff N (highBVExponent 10:ℝ) :=
    source_modulus_of_log _ m N (by omega) hGlobal hBudget
  have hBV : (∑ q∈Icc 1 (panModulusCutoff N (highBVExponent 10:ℝ)),
      BombieriVinogradov.standardPrimeAPPrefixMaxError N q)≤ C*N/log (N:ℝ)^3 := by
    simpa only [C,one_mul] using base_bv_order_three hN
  let D := (jurkatRichertSourceSiftingProduct N).divisors.filter
    (fun q : ℕ => (q : ℝ) ≤ (N : ℝ) ^ (1 / 2 - 1 / (m : ℝ)))
  let E := jurkatRichertSourceExceptionalPrimes N
  let Q := Finset.Icc 1 (LiuWeight.panModulusCutoff N (highBVExponent 10 : ℝ))
  have hDsub : D ⊆ Q := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hdiv, hlevel⟩
    have hq0 : q ≠ 0 := by
      intro hz
      have hdiv' := Nat.dvd_of_mem_divisors hdiv
      rw [hz] at hdiv'
      exact jurkatRichertSourceSiftingProduct_ne_zero N (by simpa using hdiv')
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hq0,
      (Nat.le_floor hlevel).trans hcut⟩
  have hmax : (∑ q ∈ D, BombieriVinogradov.standardPrimeAPMaxError N q) ≤
      C * (N : ℝ) / Real.log N ^ (3 : ℕ) := by
    calc
      _ ≤ ∑ q ∈ Q, BombieriVinogradov.standardPrimeAPMaxError N q :=
        Finset.sum_le_sum_of_subset_of_nonneg hDsub
          (fun q _ _ => BombieriVinogradov.standardPrimeAPMaxError_nonneg N q)
      _ ≤ ∑ q ∈ Q, BombieriVinogradov.standardPrimeAPPrefixMaxError N q :=
        BombieriVinogradov.sum_standardPrimeAPMaxError_le_prefixMaxError N Q
      _ ≤ _ := hBV
  have hcoef : C ≤ (1 / (4 * (d : ℝ))) * Real.log N := by
    calc
      C ≤ Real.log N / (4 * (d : ℝ)) := by
        apply (le_div_iff₀ (by positivity : 0 < 4 * (d : ℝ))).mpr
        nlinarith only [hC, hL, hdR, show (0 : ℝ) ≤ b from Nat.cast_nonneg b]
      _ = _ := by ring
  have hmaxPaid : (∑ q ∈ D, BombieriVinogradov.standardPrimeAPMaxError N q) ≤
      (1 / (4 * (d : ℝ))) * N / Real.log N ^ (2 : ℕ) := by
    apply hmax.trans
    apply (div_le_div_iff₀ (pow_pos hlog 3) (pow_pos hlog 2)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hcoef
      (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg (Real.log (N : ℝ))))]
  have hgrowth : 16 * (d : ℝ) * Real.log N ^ (3 : ℕ) ≤ Real.sqrt N := by
    calc
      _ ≤ Real.log N * Real.log N ^ (3 : ℕ) :=
        mul_le_mul_of_nonneg_right (by
          nlinarith only [hL, hdR, show (0 : ℝ) ≤ b from Nat.cast_nonneg b])
          (pow_nonneg hlog.le 3)
      _ = Real.log N ^ (4 : ℕ) := by ring
      _ ≤ _ := log_pow_le_sqrt_explicit hfour
  have hendpointPaid : (D.card : ℝ) * E.card ≤
      (1 / (4 * (d : ℝ))) * N / Real.log N ^ (2 : ℕ) := by
    have hep := jurkatRichertSource_exceptional_endpoint_le N (1 / (m : ℝ))
      (by omega) heps hepsHalf
    have hp : (N : ℝ) ^ (1 / 2 - 1 / (m : ℝ)) ≤ Real.sqrt N := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only [heps])
    have hlogtwo : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hstep : 2 * (N : ℝ) ^ (1 / 2 - 1 / (m : ℝ)) * Real.log N / Real.log 2 ≤
        4 * Real.sqrt N * Real.log N := by
      apply (div_le_iff₀ (by linarith only [hlogtwo])).mpr
      have hmul := mul_le_mul_of_nonneg_right hp hlog.le
      have hmul2 := mul_le_mul_of_nonneg_right hlogtwo.le
        (show 0 ≤ 4 * Real.sqrt N * Real.log N by positivity)
      nlinarith only [hmul, hmul2]
    have hfinal : 4 * Real.sqrt N * Real.log N ≤
        (1 / (4 * (d : ℝ))) * N / Real.log N ^ (2 : ℕ) := by
      apply (le_div_iff₀ (pow_pos hlog 2)).mpr
      have hs := mul_le_mul_of_nonneg_right hgrowth (Real.sqrt_nonneg (N : ℝ))
      rw [Real.mul_self_sqrt hN0.le] at hs
      calc
        _ ≤ (N : ℝ) / (4 * (d : ℝ)) := by
          apply (le_div_iff₀ (by positivity : 0 < 4 * (d : ℝ))).mpr
          nlinarith only [hs]
        _ = _ := by ring
    exact hep.trans (hstep.trans hfinal)
  have hreduction := jurkatRichertSourceRemainderSum_le_standardMax_add_exceptional
    N (1 / (m : ℝ)) hEven (by omega)
  have hS := half_le_liuSingularSeries N
  have hscale : 0 ≤ (N : ℝ) / Real.log N ^ (2 : ℕ) := by positivity
  calc
    _ ≤ (∑ q ∈ D, BombieriVinogradov.standardPrimeAPMaxError N q) +
          (D.card : ℝ) * E.card := hreduction
    _ ≤ (1 / (4 * (d : ℝ))) * N / Real.log N ^ (2 : ℕ) +
          (1 / (4 * (d : ℝ))) * N / Real.log N ^ (2 : ℕ) :=
      add_le_add hmaxPaid hendpointPaid
    _ = (1 / (d : ℝ)) * (1 / 2) * (N : ℝ) / Real.log N ^ (2 : ℕ) := by ring
    _ ≤ _ := by
      have hc := mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ 1 / (d : ℝ))
      simpa only [mul_div_assoc, mul_assoc] using mul_le_mul_of_nonneg_right hc hscale


#print axioms base_distribution_paid
end ChenEffective.H29

end
end

/- Derived from BJSH30Budget; checked as new H29 proof source. -/
section

noncomputable section
namespace ChenEffective.H29
open ChenEffective.H30
open Real
open MathlibNt.SieveTheory SwitchingPrinciple
set_option maxHeartbeats 3000000

theorem medium_mass_allocation {B J : ℝ} (hB : B≤25/2) (hJ : J≤120) :
    (B+300/5000000)*(J+1/10000+(7/125)*(8/5))+1/5000000≤B*J+113/100 := by
  nlinarith only [hB,hJ]

theorem target_margin : (jointSelbergBudget (8.2:ℝ) (1/10000) 0 (1/100)).margin=0.000926 := by
  rw [joint_selberg_margin]
  norm_num

theorem fixed_base_distribution {N : ℕ} (hN : distributionThreshold≤N) (hEven : Even N) :
    jurkatRichertSourceRemainderSum N (1/(300000000:ℝ))≤
      (1/20000000:ℝ)*SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2 := by
  exact base_distribution_paid 300000000 20000000 N (by norm_num) (by norm_num) (by norm_num)
    hN (by norm_num [highBVExponent]) hEven

theorem fixed_varying_distribution {N : ℕ} (hN : distributionThreshold≤N) (hEven : Even N) :
    jurkatRichertSourceVaryingQRemainderSum N (1/(300000000:ℝ))≤
      (1/5000000:ℝ)*SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2 := by
  exact varying_distribution_paid 300000000 5000000 N (by norm_num) (by norm_num) (by norm_num)
    hN (by norm_num [highBVExponent,weightedSaving]) hEven

#print axioms fixed_base_distribution
#print axioms fixed_varying_distribution
end ChenEffective.H29

end
end
