import ExplicitBVHigh
import ExplicitBVPayload
import ExplicitLowConductor

/-! Finite BV assembly with numerical high/payload constants. The only
remaining hypotheses are the displayed pointwise low and principal inputs.
No eventual filters or existential constants occur in these statements. -/
namespace ChenEffective
open AnalyticNumberTheory.LargeSieve
open MathlibNt.SieveTheory
open Finset
noncomputable section

def bvThreshold (A nPsi nPrincipal : ℕ) : ℕ :=
  max (highBVThreshold A) (max nPsi nPrincipal)

def bvConstant (Kpsi Kprincipal : ℝ) : ℝ :=
  32 * Kpsi + 4 * Kprincipal + 1000000000000012180

theorem explicit_principal_payment
    (N Q A : ℕ) (hN : 8 ≤ N) (hQ : Q ≤ N)
    (K : ℝ) (hK : 0 < K)
    (hPrincipal : globalPartialSummationSource N ≤
      K * (N : ℝ) / Real.log N ^ (A + 3)) :
    discreteAbelAmplifierPrefixMax N * principalGlobalPhysical N Q +
        chebyshevToLiPhysical N Q ≤ 4 * K * (N : ℝ) / Real.log N ^ A := by
  have hlog := log_one_le_of_eight_le hN
  have hlog0 : 0 < Real.log (N : ℝ) := by linarith only [hlog]
  have hlogQ : Real.log (Q : ℝ) ≤ Real.log (N : ℝ) := by
    by_cases hQ0 : Q = 0
    · simp only [hQ0, Nat.cast_zero, Real.log_zero]
      linarith only [hlog]
    · exact Real.log_le_log (by positivity) (by exact_mod_cast hQ)
  have hH : conductorHarmonicFactor Q ≤ 2 * Real.log N :=
    (conductorHarmonicFactor_le Q).trans (by linarith only [hlog, hlogQ])
  have hH0 := conductorHarmonicFactor_nonneg Q
  have hHsq : conductorHarmonicFactor Q ^ 2 ≤ 4 * Real.log N ^ 2 := by nlinarith only [hH, hH0]
  have hbound0 : 0 ≤ K * (N : ℝ) / Real.log N ^ (A + 3) := by positivity
  calc
    _ ≤ conductorHarmonicFactor Q ^ 2 * globalPartialSummationSource N :=
      principalGlobal_add_chebyshevToLi_le_qOne N Q
    _ ≤ conductorHarmonicFactor Q ^ 2 *
        (K * (N : ℝ) / Real.log N ^ (A + 3)) :=
      mul_le_mul_of_nonneg_left hPrincipal (sq_nonneg _)
    _ ≤ (4 * Real.log N ^ 2) *
        (K * (N : ℝ) / Real.log N ^ (A + 3)) :=
      mul_le_mul_of_nonneg_right hHsq hbound0
    _ ≤ 4 * K * (N : ℝ) / Real.log N ^ A := by
      rw [pow_add]
      field_simp
      exact hlog

/-- A finite Standard-BV bound. The primitive exponent and conductor range
are fixed numerically from A; only the two analytic input estimates remain. -/
theorem explicit_BV_at
    (A N : ℕ) (hcut : highBVThreshold A ≤ N)
    (Kpsi Kprincipal : ℝ) (hKpsi : 0 < Kpsi) (hKprincipal : 0 < Kprincipal)
    (hPsi : ∀ d ∈ Finset.Icc 2 (logConductorThreshold N (highBVConductorExponent A)),
      ∀ ψ : PrimitiveCharacter d, ψ.1 ≠ 1 →
        primitivePrefixAmplitude vonMangoldtIntegerCoeff N d ψ ≤
          Kpsi * (N : ℝ) / Real.log N ^ (A + highBVConductorExponent A + 5))
    (hPrincipal : globalPartialSummationSource N ≤
      Kprincipal * (N : ℝ) / Real.log N ^ (A + 3)) :
    (∑ q ∈ Finset.Icc 1 (LiuWeight.panModulusCutoff N (highBVExponent A : ℝ)),
      BombieriVinogradov.standardPrimeAPPrefixMaxError N q) ≤
        bvConstant Kpsi Kprincipal * (N : ℝ) / Real.log N ^ A := by
  have hN9 : 9 ≤ N := (logPowerCutoff_nine_le _).trans hcut
  let B := highBVExponent A
  let C := highBVConductorExponent A
  let Q := LiuWeight.panModulusCutoff N (B : ℝ)
  let R := logConductorThreshold N C
  have hlow := explicit_low_conductor_payment (by omega : 8 ≤ N) A C B Kpsi hKpsi hPsi
  have hglobal := explicit_principal_payment N Q A (by omega)
    (panModulusCutoff_le_self (by omega) B) Kprincipal hKprincipal hPrincipal
  have hcombined :
      2 * discreteAbelAmplifierPrefixMax N * lowConductorPhysical N Q C +
        discreteAbelAmplifierPrefixMax N * principalGlobalPhysical N Q +
        chebyshevToLiPhysical N Q ≤
      (32 * Kpsi + 4 * Kprincipal) * (N : ℝ) / Real.log N ^ A := by
    calc
      _ = (2 * discreteAbelAmplifierPrefixMax N * lowConductorPhysical N Q C) +
          (discreteAbelAmplifierPrefixMax N * principalGlobalPhysical N Q +
            chebyshevToLiPhysical N Q) := by ring
      _ ≤ 32 * Kpsi * (N : ℝ) / Real.log N ^ A +
          4 * Kprincipal * (N : ℝ) / Real.log N ^ A := add_le_add hlow hglobal
      _ = _ := by ring
  have hhigh := explicit_high_payment A N hcut
  have hlog := log_one_le_of_eight_le (by omega : 8 ≤ N)
  have hB : A + 3 ≤ B := by dsimp [B, highBVExponent]; omega
  have hQbound : (Q : ℝ) ≤ Real.sqrt N / Real.log N ^ (A + 3) := by
    calc
      (Q : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ (B : ℝ) :=
        Nat.floor_le (by positivity)
      _ = Real.sqrt N / Real.log N ^ B := by rw [Real.sqrt_eq_rpow, Real.rpow_natCast]
      _ ≤ Real.sqrt N / Real.log N ^ (A + 3) :=
        div_le_div_of_nonneg_left (Real.sqrt_nonneg _)
          (pow_pos (by linarith only [hlog]) _) (pow_le_pow_right₀ hlog hB)
  have hpayload := explicit_payload_payment A N (by omega) Q hQbound
  have hclosed := standardBV_sufficient_at_closed A B C N Q R R
    (32 * Kpsi + 4 * Kprincipal) 1000000000000012000 (by omega) rfl hcombined hhigh hpayload
  convert hclosed using 1
  unfold bvConstant
  ring

/-- The starting point of the assembled BV estimate is exactly the maximum
of the numerical high threshold and the two analytic input thresholds. -/
theorem explicit_BV_of_inputs
    (A nPsi nPrincipal : ℕ) (Kpsi Kprincipal : ℝ)
    (hKpsi : 0 < Kpsi) (hKprincipal : 0 < Kprincipal)
    (hPsi : ∀ N : ℕ, nPsi ≤ N →
      ∀ d ∈ Finset.Icc 2 (logConductorThreshold N (highBVConductorExponent A)),
      ∀ ψ : PrimitiveCharacter d, ψ.1 ≠ 1 →
        primitivePrefixAmplitude vonMangoldtIntegerCoeff N d ψ ≤
          Kpsi * (N : ℝ) / Real.log N ^ (A + highBVConductorExponent A + 5))
    (hPrincipal : ∀ N : ℕ, nPrincipal ≤ N → globalPartialSummationSource N ≤
      Kprincipal * (N : ℝ) / Real.log N ^ (A + 3))
    {N : ℕ} (hN : bvThreshold A nPsi nPrincipal ≤ N) :
    (∑ q ∈ Finset.Icc 1 (LiuWeight.panModulusCutoff N (highBVExponent A : ℝ)),
      BombieriVinogradov.standardPrimeAPPrefixMaxError N q) ≤
        bvConstant Kpsi Kprincipal * (N : ℝ) / Real.log N ^ A := by
  have hh : highBVThreshold A ≤ N := (le_max_left _ _).trans hN
  have hp : nPsi ≤ N := by unfold bvThreshold at hN; omega
  have hg : nPrincipal ≤ N := by unfold bvThreshold at hN; omega
  exact explicit_BV_at A N hh Kpsi Kprincipal hKpsi hKprincipal (hPsi N hp) (hPrincipal N hg)

#print axioms explicit_BV_of_inputs
end
end ChenEffective
