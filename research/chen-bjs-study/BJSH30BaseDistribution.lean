import BJSH30Distribution

noncomputable section
namespace ChenEffective.H30
open Real Finset
open MathlibNt.SieveTheory SwitchingPrinciple SingularSeries LiuWeight
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem base_distribution_paid (m d N : ℕ) (hm : 3≤ m) (hd : 0< d) (hdcap : d≤20000000)
    (hN : distributionThreshold≤ N) (hBudget : m*highBVExponent 10≤3*10^11) (hEven : Even N) :
    jurkatRichertSourceRemainderSum N (1/(m:ℝ))≤
      (1/(d:ℝ))*liuSingularSeries N*N/log (N:ℝ)^2 := by
  let b : ℕ := 1
  let C : ℝ := 1
  have hC : C≤ b := by norm_num [C,b]
  have hGlobal := distribution_log hN
  have hN9 := (distribution_parameters hN).1
  have hfour : logPowerCutoff 4≤ N := (distribution_log_cutoff (by norm_num : 16*((4:ℕ)+1)^2≤10^13)).trans hN
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
end ChenEffective.H30
