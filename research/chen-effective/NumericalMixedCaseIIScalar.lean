import NumericalMixedFinish

namespace ChenEffective
open Real Set
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def mixedCubicPerturbation : ℝ := 7 * (3 : ℝ) ^ (16 : ℕ)

theorem mixed_gate_power_large {L : ℝ} (hcut : (logPowerCutoff 32 : ℝ) ≤ L) :
    (10 ^ 12 : ℝ) ≤ L ^ (1 / 8 : ℝ) := by
  have hL9 := real_log_power_cutoff_nine hcut
  have hL0 : 0 < L := by linarith only [hL9]
  have hl := real_log_power_cutoff_log hcut
  norm_num only [Nat.cast_ofNat] at hl
  have hten : (10 : ℝ) ≤ Real.exp 10 := by linarith only [Real.add_one_le_exp (10 : ℝ)]
  have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) hten 12
  rw [← Real.exp_nat_mul] at hh
  rw [Real.rpow_def_of_pos hL0]
  apply hh.trans (Real.exp_le_exp.mpr ?_)
  nlinarith only [hl]

theorem mixed_caseII_small_parameter {D K : ℝ} (hD : 1 < D)
    (hcut : (logPowerCutoff 32 : ℝ) ≤ Real.log D) (hK : 2 ≤ K)
    (hKlevel : K ^ (7 : ℝ) ≤ Real.log D) :
    K * sourceSigma D 16 * (Real.log D) ^ (-(1 / 2 : ℝ)) ≤ 1 / (10 ^ 12 : ℝ) := by
  let L := Real.log D
  have hL : 0 < L := Real.log_pos hD
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hK4 : K ^ (4 : ℝ) ≤ L :=
    (Real.rpow_le_rpow_of_exponent_le (by linarith only [hK] : 1 ≤ K)
      (by norm_num : (4 : ℝ) ≤ 7)).trans hKlevel
  have hKr : K ≤ L ^ (1 / 4 : ℝ) := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hK0 _) hK4 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [← Real.rpow_mul hK0] at hh
    norm_num at hh
    exact hh
  have hσ := polynomial_sourceSigma_upper hD hcut
  have hroot := mixed_gate_power_large hcut
  have hσ0 : 0 ≤ sourceSigma D 16 := by
    have hD2 : 2 ≤ D := by
      have hh := Real.log_le_sub_one_of_pos (zero_lt_one.trans hD)
      have hL9 := real_log_power_cutoff_nine hcut
      linarith only [hh, hL9]
    have hi : 1 < Real.log (27 * D) := by
      apply (Real.lt_log_iff_exp_lt (by positivity)).mpr
      linarith only [Real.exp_one_lt_d9, hD2]
    unfold sourceSigma
    exact (mul_pos (Real.rpow_pos_of_pos hL _) (Real.log_pos hi)).le
  calc
    _ ≤ L ^ (1 / 4 : ℝ) * L ^ (1 / 8 : ℝ) * L ^ (-(1 / 2 : ℝ)) := by
      gcongr
    _ = L ^ (-(1 / 8 : ℝ)) := by
      rw [← Real.rpow_add hL, ← Real.rpow_add hL]
      norm_num
    _ ≤ _ := by
      rw [Real.rpow_neg hL.le, one_div]
      simpa only [one_div] using (inv_le_inv₀ (Real.rpow_pos_of_pos hL (1 / 8 : ℝ))
        (by norm_num : (0 : ℝ) < 10 ^ 12)).mpr hroot

theorem mixed_caseII_scalar {L σ K s F A3 A C : ℝ}
    (hL : 1 ≤ L) (hσ : 3 ≤ σ) (hK : 2 ≤ K) (hs : 1 < s)
    (hQ : mixedCubicPerturbation ≤ L)
    (hsmall : K * σ * L ^ (-(1 / 2 : ℝ)) ≤ 1 / (10 ^ 12 : ℝ))
    (hF : F ≤ 864)
    (hA : (1 / 3 : ℝ) * L ^ (-(1 / 2 : ℝ)) ≤ A) (hC : 1 ≤ C)
    (htransfer : (3 / s) * A3 ≤ (1 + mixedCubicPerturbation / L) * A) :
    (3 / s) * (1 + 3 * K / L) * (F + C * (1 - 1 / (10 * σ)) * A3) +
      9 * K / (s * L) ≤ (3 / s) * F + C * A := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hσ0 : 0 < σ := by linarith only [hσ]
  have hs0 : 0 < s := zero_lt_one.trans hs
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hA0 : 0 ≤ A := (by positivity : (0 : ℝ) ≤ (1 / 3) * L ^ (-(1 / 2 : ℝ))).trans hA
  have hu : 0 < L ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hL0 _
  have hu2 : (L ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / L := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    norm_num [Real.rpow_neg_one]
  have hi : 1 / L ≤ L ^ (-(1 / 2 : ℝ)) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hkbase : K * σ / L ≤ K * σ * L ^ (-(1 / 2 : ℝ)) := by
    simpa only [div_eq_mul_inv, one_mul, mul_assoc] using mul_le_mul_of_nonneg_left hi
      (mul_nonneg hK0 hσ0.le)
  have hbase : σ / L ≤ K * σ * L ^ (-(1 / 2 : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hi hσ0.le
    have hp := mul_nonneg (show 0 ≤ K - 1 by linarith only [hK]) (mul_nonneg hσ0.le hu.le)
    simp only [div_eq_mul_inv, one_mul] at *
    nlinarith only [hh, hp]
  have hgrowth : (6 * K + 2 * mixedCubicPerturbation) / L ≤ 1 / (100 * σ) := by
    have hh := mul_le_mul_of_nonneg_left hbase
      (by norm_num [mixedCubicPerturbation] : 0 ≤ 2 * mixedCubicPerturbation)
    have hh' := mul_le_mul_of_nonneg_left hkbase (by norm_num : (0 : ℝ) ≤ 6)
    have hp := mul_le_mul_of_nonneg_left hsmall
      (by norm_num [mixedCubicPerturbation] : 0 ≤ 6 + 2 * mixedCubicPerturbation)
    apply (le_div_iff₀ (by positivity : 0 < 100 * σ)).mpr
    norm_num [mixedCubicPerturbation] at hh hh' hp ⊢
    ring_nf at hh hh' hp ⊢
    nlinarith only [hh, hh', hp]
  have hr0 : 0 ≤ 1 - 1 / (10 * σ) := by
    have hh : 1 / (10 * σ) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith only [hσ])
    linarith only [hh]
  have hr1 : 1 - 1 / (10 * σ) ≤ 1 := by
    have hh : 0 ≤ 1 / (10 * σ) := by positivity
    linarith only [hh]
  have hcoef : (1 - 1 / (10 * σ)) * (1 + 3 * K / L) *
      (1 + mixedCubicPerturbation / L) ≤ 1 - 9 / (100 * σ) := by
    have ht : mixedCubicPerturbation / L ≤ 1 := (div_le_one hL0).mpr hQ
    have hprod := mul_le_mul_of_nonneg_left ht (show 0 ≤ 3 * K / L by positivity)
    have he : (1 + 3 * K / L) * (1 + mixedCubicPerturbation / L) ≤
        1 + (6 * K + 2 * mixedCubicPerturbation) / L := by
      have hQ0 : 0 ≤ mixedCubicPerturbation / L := by unfold mixedCubicPerturbation; positivity
      ring_nf at hprod hQ0 ⊢
      nlinarith only [hprod, hQ0]
    have hh := mul_le_mul_of_nonneg_left he hr0
    have hp := mul_le_mul_of_nonneg_right hr1
      (show 0 ≤ (6 * K + 2 * mixedCubicPerturbation) / L by unfold mixedCubicPerturbation; positivity)
    have heq : 1 - 1 / (10 * σ) + 1 / (100 * σ) = 1 - 9 / (100 * σ) := by ring
    nlinarith only [hh, hp, hgrowth, heq]
  have herr : (3 / s) * (1 + 3 * K / L) * (C * (1 - 1 / (10 * σ)) * A3) ≤
      C * (1 - 9 / (100 * σ)) * A := by
    have hh := mul_le_mul_of_nonneg_left htransfer
      (show 0 ≤ C * (1 - 1 / (10 * σ)) * (1 + 3 * K / L) by positivity)
    have hp := mul_le_mul_of_nonneg_right hcoef (mul_nonneg (by linarith only [hC]) hA0)
    nlinarith only [hh, hp]
  have hmain : (3 / s) * (1 + 3 * K / L) * F + 9 * K / (s * L) ≤
      (3 / s) * F + 7785 * K / (s * L) := by
    have hh := mul_le_mul_of_nonneg_left hF (show 0 ≤ 9 * K / (s * L) by positivity)
    ring_nf at hh ⊢
    nlinarith only [hh]
  have hloss : 7785 * K / (s * L) ≤ C * A / (100 * σ) := by
    have hh := mul_le_mul_of_nonneg_right hsmall hu.le
    rw [mul_assoc (K * σ), ← pow_two, hu2] at hh
    have hCA : A ≤ C * A := by nlinarith only [mul_le_mul_of_nonneg_right hC hA0]
    have hinv : 1 / s ≤ 1 := (div_le_one hs0).mpr hs.le
    have hm := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 7785 * K / L by positivity)
    have hn := mul_le_mul_of_nonneg_right hm hσ0.le
    apply (le_div_iff₀ (by positivity : 0 < 100 * σ)).mpr
    ring_nf at hh hA hCA hn ⊢
    nlinarith only [hh, hA, hCA, hn, hu]
  have hmargin : (1 - 9 / (100 * σ)) + 1 / (100 * σ) ≤ 1 := by
    have : 0 ≤ 1 / (100 * σ) := by positivity
    ring_nf at this ⊢
    linarith
  have hh := mul_le_mul_of_nonneg_right hmargin (mul_nonneg (by linarith only [hC]) hA0)
  ring_nf at herr hmain hloss hh ⊢
  nlinarith only [herr, hmain, hloss, hh]

#print axioms mixed_caseII_small_parameter
#print axioms mixed_caseII_scalar
end ChenEffective
