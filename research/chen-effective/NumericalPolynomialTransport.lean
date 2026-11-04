import NumericalPolynomialKernel

/-! Depth-independent bounds on the actual prime transport functional.
The high strip contracts strictly. Case II transfers a bounded error to the
compact strip; absorbing that transfer into the mixed invariant is separate.
-/

namespace ChenEffective
open Real Set MeasureTheory
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem numerical_polynomial_transport_high
    {S : BoundingSieve} {D z w s σ K : ℝ}
    (hD : 1 < D) (hz2 : 2 ≤ z) (hw2 : 2 ≤ w) (hwz : w ≤ z)
    (hz : z = D ^ (1 / s)) (hw : w = D ^ (1 / σ))
    (hs : 16 ≤ s) (hsσ : s ≤ σ)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K)
    (hlevel : 288 * K ^ 2 ≤ Real.log w) :
    suzukiLemmaEightSevenPrimeSum S D w z z polynomialTransportKernel ≤
      (11 / 12 : ℝ) / s ^ 4 := by
  have hs0 : 0 < s := by linarith only [hs]
  have hs1 : 0 < s - 1 := by linarith only [hs]
  have hlog : 0 < Real.log w := Real.log_pos (by linarith only [hw2])
  have hratio : K ^ 2 / Real.log w ≤ 1 / 288 := by
    apply (div_le_iff₀ hlog).mpr
    linarith only [hlevel]
  have hpow : s ^ 4 ≤ 2 * (s - 1) ^ 4 := by
    have hsub : 0 ≤ s - 16 := by linarith only [hs]
    have hpos : 0 ≤ (s - 16) ^ 4 + 56 * (s - 16) ^ 3 +
        1164 * (s - 16) ^ 2 + 10616 * (s - 16) + 35714 := by positivity
    nlinarith only [hpos]
  have hend : (6 * K ^ 2 * polynomialTransportKernel s / Real.log w) * (s / s) ≤
      (1 / 12 : ℝ) / s ^ 4 := by
    rw [div_self hs0.ne', mul_one, polynomialTransportKernel_eq (by linarith only [hs])]
    calc
      _ = 12 * (K ^ 2 / Real.log w) / (s - 1) ^ 4 := by ring
      _ ≤ 12 * (1 / 288 : ℝ) / (s - 1) ^ 4 := by gcongr
      _ ≤ _ := by
        apply (div_le_div_iff₀ (by positivity : 0 < (s - 1) ^ 4)
          (by positivity : 0 < s ^ 4)).mpr
        nlinarith only [hpow]
  have hh := numerical_polynomial_prime_transport hD hz2 hz2 hw2 hwz le_rfl
    hz hz hw (by linarith only [hs]) hsσ hK hlocal
  apply hh.trans
  have hi := polynomialTransportKernel_high hs hsσ
  have ha := add_le_add hi hend
  convert ha using 1
  ring

/-- The actual cubic Case-II prime sum has a fixed transfer coefficient,
including the discrete local-product endpoint remainder. -/
theorem numerical_polynomial_transport_caseII
    {S : BoundingSieve} {D z v w s σ K : ℝ}
    (hD : 1 < D) (hz2 : 2 ≤ z) (hv2 : 2 ≤ v) (hw2 : 2 ≤ w)
    (hwv : w ≤ v) (hvz : v ≤ z)
    (hz : z = D ^ (1 / s)) (hv : v = D ^ (1 / (3 : ℝ))) (hw : w = D ^ (1 / σ))
    (hs : 0 < s) (hσ : 3 ≤ σ)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K)
    (hlevel : 288 * K ^ 2 ≤ Real.log w) :
    suzukiLemmaEightSevenPrimeSum S D w v z polynomialTransportKernel ≤ 1 / (10 * s) := by
  have hlog : 0 < Real.log w := Real.log_pos (by linarith only [hw2])
  have hratio : K ^ 2 / Real.log w ≤ 1 / 288 := by
    apply (div_le_iff₀ hlog).mpr
    linarith only [hlevel]
  have hend : (6 * K ^ 2 * polynomialTransportKernel 3 / Real.log w) * (3 / s) ≤
      1 / (128 * s) := by
    rw [polynomialTransportKernel_eq (by norm_num : (2 : ℝ) ≤ 3)]
    norm_num only [show (3 : ℝ) - 1 = 2 by norm_num, Nat.reducePow]
    calc
      _ = (9 / 4 : ℝ) * (K ^ 2 / Real.log w) / s := by ring
      _ ≤ (9 / 4 : ℝ) * (1 / 288 : ℝ) / s := by gcongr
      _ = _ := by ring
  have hh := numerical_polynomial_prime_transport hD hz2 hv2 hw2 hwv hvz
    hz hv hw (by norm_num : (2 : ℝ) ≤ 3) hσ hK hlocal
  apply hh.trans
  have hi := polynomialTransportKernel_caseII hs hσ
  apply (add_le_add hi hend).trans
  field_simp
  linarith only [hs]

#print axioms numerical_polynomial_transport_high
#print axioms numerical_polynomial_transport_caseII

/-- The extra profile is deliberately unperturbed. -/
noncomputable def polynomialCorrection (D s : ℝ) : ℝ :=
  (Real.log D) ^ (-(5 / 8 : ℝ)) / s ^ 4

theorem logarithmic_correction_half {L l : ℝ} (hL : 0 < L)
    (hhalf : L ≤ 2 * l) :
    l ^ (-(5 / 8 : ℝ)) ≤ 2 * L ^ (-(5 / 8 : ℝ)) := by
  have hbase : L / 2 ≤ l := by linarith only [hhalf]
  have hp := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < L / 2)
    hbase (by norm_num : -(5 / 8 : ℝ) ≤ 0)
  have htwo : (2 : ℝ) ^ (5 / 8 : ℝ) ≤ 2 :=
    Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  calc
    _ ≤ (L / 2) ^ (-(5 / 8 : ℝ)) := hp
    _ = L ^ (-(5 / 8 : ℝ)) * (2 : ℝ) ^ (5 / 8 : ℝ) := by
      rw [Real.div_rpow hL.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
    _ ≤ _ := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left htwo
        (Real.rpow_nonneg hL.le (-(5 / 8 : ℝ)))

/-- The actual ceiling quotient and its actual recursive coordinate fit the
same kernel used above. This includes cubic Case-II primes. -/
theorem polynomialCorrection_recursive {D p : ℕ} (hp : 2 ≤ p) (hpsq : p ^ 2 ≤ D) :
    polynomialCorrection (D ⌈/⌉ p : ℕ)
        (SuzukiLemma144Equation1410.recursiveCoordinate D p) ≤
      (Real.log (D : ℝ)) ^ (-(5 / 8 : ℝ)) *
        polynomialTransportKernel (Real.log (D : ℝ) / Real.log (p : ℝ)) := by
  have hD2 : 2 ≤ D := by nlinarith only [hp, hpsq]
  have hL : 0 < Real.log (D : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < D by omega))
  have hlp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have h2p : 2 * p ≤ D := by nlinarith only [hp, hpsq]
  have hq2 : 2 ≤ D ⌈/⌉ p := by
    have hh := (ceilDiv_le_iff_le_mul (show 0 < p by omega)).mp (le_refl (D ⌈/⌉ p))
    nlinarith only [hh, h2p, hp]
  have hlq : 0 < Real.log ((D ⌈/⌉ p : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < D ⌈/⌉ p by omega))
  have hr : 2 ≤ Real.log (D : ℝ) / Real.log (p : ℝ) := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < (p : ℝ) ^ 2)
      (show (p : ℝ) ^ 2 ≤ (D : ℝ) by exact_mod_cast hpsq)
    rw [Real.log_pow] at hh
    apply (le_div_iff₀ hlp).mpr
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh]
  have hcoord := (SuzukiLemma144Equation1410.coordinate_bounds hp h2p).1
  have hin : 1 ≤ SuzukiLemma144Equation1410.inheritedCoordinate D p := by
    unfold SuzukiLemma144Equation1410.inheritedCoordinate
    linarith only [hr]
  have hcpos : 0 < SuzukiLemma144Equation1410.recursiveCoordinate D p := by linarith only [hcoord, hin]
  have hweight := logarithmic_correction_half hL (recursive_log_half hp hpsq)
  have hden := pow_le_pow_left₀ (by linarith only [hin] :
    0 ≤ SuzukiLemma144Equation1410.inheritedCoordinate D p) hcoord 4
  unfold polynomialCorrection
  calc
    _ ≤ (2 * (Real.log (D : ℝ)) ^ (-(5 / 8 : ℝ))) /
        (SuzukiLemma144Equation1410.inheritedCoordinate D p) ^ 4 :=
      div_le_div₀ (by positivity) hweight (by positivity) hden
    _ = _ := by
      rw [polynomialTransportKernel_eq hr]
      unfold SuzukiLemma144Equation1410.inheritedCoordinate
      ring

#print axioms polynomialCorrection_recursive
end ChenEffective
