import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVLowSiegelWalfiszProducer

/-!
Finite version of the nonprincipal low-conductor summation step.
Adapted from StandardBVLowSiegelWalfiszProducer in this repository;
see the repository's Apache-2.0 LICENSE.
The pointwise analytic bound is an explicit hypothesis, not an axiom.
This removes the eventual scalar-envelope cutoff: N >= 8 suffices for it.
-/
namespace ChenEffective

open AnalyticNumberTheory.LargeSieve
open Finset

theorem log_one_le_of_eight_le {N : ℕ} (hN : 8 ≤ N) :
    1 ≤ Real.log (N : ℝ) := by
  have h8 : (1 : ℝ) < Real.log 8 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_gt_d9]
  exact h8.le.trans (Real.log_le_log (by norm_num : (0 : ℝ) < 8)
    (show (8 : ℝ) ≤ N by exact_mod_cast hN))

theorem panModulusCutoff_le_self {N : ℕ} (hN : 8 ≤ N) (B : ℕ) :
    MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ) ≤ N := by
  have hlog := log_one_le_of_eight_le hN
  have hden : 1 ≤ Real.log (N : ℝ) ^ (B : ℝ) :=
    Real.one_le_rpow hlog (by positivity)
  have hsqrt : Real.sqrt (N : ℝ) ≤ N := by
    have h1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    exact (Real.sqrt_le_iff).2 ⟨by positivity, by nlinarith⟩
  unfold MathlibNt.SieveTheory.LiuWeight.panModulusCutoff
  apply Nat.floor_le_of_le
  calc
    (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ (B : ℝ) ≤
        (N : ℝ) ^ (1 / 2 : ℝ) := div_le_self (Real.rpow_nonneg (by positivity) _) hden
    _ = Real.sqrt (N : ℝ) := by rw [Real.sqrt_eq_rpow]
    _ ≤ N := hsqrt

theorem low_scalar_envelopes_at_eight {N : ℕ} (hN : 8 ≤ N) (C B : ℕ) :
    let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
    lowConductorArithmeticMass N Q C ≤ 4 * Real.log N ^ (C + 2) ∧
      conductorHarmonicFactor Q ^ 2 ≤ 4 * Real.log N ^ 2 := by
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
  have hQN : Q ≤ N := panModulusCutoff_le_self hN B
  have hlog := log_one_le_of_eight_le hN
  have hlogQ : Real.log (Q : ℝ) ≤ Real.log (N : ℝ) := by
    by_cases hQ : Q = 0
    · rw [hQ, Nat.cast_zero, Real.log_zero]
      linarith
    · exact Real.log_le_log (by positivity) (by exact_mod_cast hQN)
  have hH : conductorHarmonicFactor Q ≤ 2 * Real.log N :=
    (conductorHarmonicFactor_le Q).trans (by linarith)
  have hH0 := conductorHarmonicFactor_nonneg Q
  have hR : (logConductorThreshold N C : ℝ) ≤ Real.log N ^ C := by
    unfold logConductorThreshold
    exact_mod_cast Nat.floor_le (pow_nonneg (by positivity) C)
  constructor
  · refine (lowConductorArithmeticMass_le_explicit N Q C).trans ?_
    calc
      (logConductorThreshold N C : ℝ) * conductorHarmonicFactor Q ^ 2 ≤
          Real.log N ^ C * (2 * Real.log N) ^ 2 := by gcongr
      _ = 4 * Real.log N ^ (C + 2) := by rw [pow_add]; ring
  · nlinarith

/-- Given a numerical primitive-prefix bound at N, the entire nonprincipal
low-conductor contribution has the displayed constant, already for N >= 8.
The principal/PNT contribution is deliberately kept separate. -/
theorem explicit_low_conductor_payment
    {N : ℕ} (hN : 8 ≤ N) (A C B : ℕ) (K : ℝ) (hK : 0 < K)
    (hPsi : ∀ d ∈ Finset.Icc 2 (logConductorThreshold N C),
      ∀ ψ : PrimitiveCharacter d, ψ.1 ≠ 1 →
        primitivePrefixAmplitude vonMangoldtIntegerCoeff N d ψ ≤
          K * (N : ℝ) / Real.log N ^ (A + C + 5)) :
    2 * discreteAbelAmplifierPrefixMax N *
        lowConductorPhysical N (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)) C ≤
      32 * K * (N : ℝ) / Real.log N ^ A := by
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
  have hlog := log_one_le_of_eight_le hN
  have hlog0 : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  have hX0 : 0 ≤ K * (N : ℝ) / Real.log N ^ (A + C + 5) := by positivity
  have hlowPoint : ∀ d ∈ lowConductorSet N Q C, ∀ ψ : PrimitiveCharacter d,
      primitivePrefixAmplitude vonMangoldtIntegerCoeff N d ψ ≤
        K * (N : ℝ) / Real.log N ^ (A + C + 5) := by
    intro d hd ψ
    apply hPsi d
    · exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1,
        (Finset.mem_filter.mp hd).2⟩
    · exact primitiveCharacter_ne_one_of_two_le
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1 ψ
  have hlow := lowConductorPhysical_le_of_primitivePrefix N Q C _ hX0 hlowPoint
  have henv := (low_scalar_envelopes_at_eight hN C B).1
  have habel4 : discreteAbelAmplifierPrefixMax N ≤ 4 := by
    refine (discreteAbelAmplifierPrefixMax_le_two_inv_log_two N).trans ?_
    have hlt : (1 / 2 : ℝ) < Real.log 2 := Real.log_two_gt_d9.trans' (by norm_num)
    have hinv : (Real.log 2)⁻¹ < 2 := by
      rw [inv_eq_one_div, one_div_lt (Real.log_pos (by norm_num)) (by norm_num)]
      norm_num
      exact hlt
    linarith
  have hlow0 : 0 ≤ lowConductorPhysical N Q C := by
    unfold lowConductorPhysical directConductorMeanOn
    apply Finset.sum_nonneg
    intro d hd
    apply mul_nonneg
    · unfold directConductorWeight
      positivity
    · exact Finset.sum_nonneg fun ψ _ =>
        primitivePrefixAmplitude_nonneg vonMangoldtIntegerCoeff N d ψ
  calc
    _ ≤ 2 * 4 * lowConductorPhysical N Q C := by gcongr
    _ ≤ 2 * 4 * (4 * Real.log N ^ (C + 2) *
          (K * (N : ℝ) / Real.log N ^ (A + C + 5))) := by
      gcongr
      exact hlow.trans (mul_le_mul_of_nonneg_right henv hX0)
    _ ≤ 32 * K * (N : ℝ) / Real.log N ^ A := by
      rw [pow_add, pow_add]
      field_simp
      have hpowAC : 0 ≤ Real.log (N : ℝ) ^ (A + C) := by positivity
      have hlog3 : 1 ≤ Real.log (N : ℝ) ^ 3 := one_le_pow₀ hlog
      have hpowmul : Real.log (N : ℝ) ^ C * Real.log (N : ℝ) ^ A =
          Real.log (N : ℝ) ^ (A + C) := by rw [← pow_add]; congr 1; omega
      calc
        2 * 4 ^ 2 * Real.log (N : ℝ) ^ C * Real.log (N : ℝ) ^ A =
            32 * (Real.log (N : ℝ) ^ C * Real.log (N : ℝ) ^ A) := by ring
        _ = 32 * Real.log (N : ℝ) ^ (A + C) := by rw [hpowmul]
        _ ≤ 32 * (Real.log (N : ℝ) ^ 3 * Real.log (N : ℝ) ^ (A + C)) := by
          exact mul_le_mul_of_nonneg_left
            (by simpa using mul_le_mul_of_nonneg_right hlog3 hpowAC) (by norm_num)
        _ = Real.log (N : ℝ) ^ 3 * Real.log (N : ℝ) ^ (A + C) * 32 := by ring

#print axioms explicit_low_conductor_payment
end ChenEffective
