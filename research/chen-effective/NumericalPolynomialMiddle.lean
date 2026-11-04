import NumericalPolynomialTransport
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSigmaTwelveGlobalScaling

/-! Natural-ceiling versions of the polynomial transport estimates. These
are the literal inherited error sums needed by a mixed-error induction. -/

open scoped Classical BigOperators
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open SuzukiLemma144Equation1410 SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem middle_prime_square_le {D p : ℕ} {τ : ℝ}
    (hD : 1 < (D : ℝ)) (hτ : 2 ≤ τ) (hp : (p : ℝ) < (D : ℝ) ^ (1 / τ)) :
    p ^ 2 ≤ D := by
  have hroot : (D : ℝ) ^ (1 / τ) ≤ Real.sqrt (D : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hD.le
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hτ)
  have hsquare := (sq_le_sq₀ (Nat.cast_nonneg p) (Real.sqrt_nonneg (D : ℝ))).mpr
    (hp.le.trans hroot)
  rw [Real.sq_sqrt (Nat.cast_nonneg D)] at hsquare
  exact_mod_cast hsquare

noncomputable def polynomialInheritedSum (S : BoundingSieve) (D znat : ℕ) (σ τ : ℝ) : ℝ :=
  ∑ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ τ,
    S.nu p * suzukiVProduct S (p : ℝ) / suzukiVProduct S (znat : ℝ) *
      polynomialCorrection (D ⌈/⌉ p : ℕ) (recursiveCoordinate D p)

/-- The production inherited sum is bounded using the actual ceiling
quotient, rather than replacing it by real division in the induction input. -/
theorem polynomialInheritedSum_le_prime_sum
    (S : BoundingSieve) {D znat : ℕ} {w v s τ σ : ℝ}
    (hD : 1 < (D : ℝ)) (hτ : 2 ≤ τ)
    (hvz : v ≤ (D : ℝ) ^ (1 / s))
    (hz : znat = ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hv : v = (D : ℝ) ^ (1 / τ)) (hw : w = (D : ℝ) ^ (1 / σ)) :
    polynomialInheritedSum S D znat σ τ ≤
      (Real.log (D : ℝ)) ^ (-(5 / 8 : ℝ)) *
        suzukiLemmaEightSevenPrimeSum S (D : ℝ) w v ((D : ℝ) ^ (1 / s))
          polynomialTransportKernel := by
  classical
  let z := (D : ℝ) ^ (1 / s)
  have hz0 : 0 < z := Real.rpow_pos_of_pos (by linarith only [hD]) _
  have hV : suzukiVProduct S (znat : ℝ) = suzukiVProduct S z :=
    suzukiVProduct_natCeil_eq_power S hz0 hz
  have hc : sigmaOneCarrier S.prodPrimes.primeFactors D σ τ =
      S.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < v) := by
    ext p
    simp only [sigmaOneCarrier, Finset.mem_filter]
    rw [hw, hv]
  unfold polynomialInheritedSum suzukiLemmaEightSevenPrimeSum
  rw [hc, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hpS, hpw, hpv⟩ := Finset.mem_filter.mp hp
  have hpPrime := Nat.prime_of_mem_primeFactors hpS
  have hpx : (p : ℝ) < z := hpv.trans_le hvz
  have hnu : 0 ≤ S.nu p :=
    (S.nu_pos_of_prime p hpPrime (Nat.mem_primeFactors.mp hpS).2.1).le
  have hratio : 0 ≤ suzukiVProduct S (p : ℝ) / suzukiVProduct S (znat : ℝ) :=
    div_nonneg (suzukiVProduct_pos S _).le (suzukiVProduct_pos S _).le
  have hh := mul_le_mul_of_nonneg_left
    (polynomialCorrection_recursive hpPrime.two_le
      (middle_prime_square_le hD hτ (by simpa only [hv] using hpv)))
    (mul_nonneg hnu hratio)
  rw [show S.nu p * suzukiVProduct S (p : ℝ) / suzukiVProduct S (znat : ℝ) =
      S.nu p * (suzukiVProduct S (p : ℝ) / suzukiVProduct S (znat : ℝ)) by ring]
  rw [hV, suzukiVProduct_div_eq_suffix S hpx] at hh ⊢
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hh

theorem polynomialInheritedSum_high
    {S : BoundingSieve} {D znat : ℕ} {w s σ K : ℝ}
    (hD : 1 < (D : ℝ)) (hz2 : 2 ≤ (D : ℝ) ^ (1 / s)) (hw2 : 2 ≤ w)
    (hwz : w ≤ (D : ℝ) ^ (1 / s))
    (hz : znat = ⌈(D : ℝ) ^ (1 / s)⌉₊) (hw : w = (D : ℝ) ^ (1 / σ))
    (hs : 16 ≤ s) (hsσ : s ≤ σ)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K)
    (hlevel : 288 * K ^ 2 ≤ Real.log w) :
    polynomialInheritedSum S D znat σ s ≤ (11 / 12 : ℝ) * polynomialCorrection D s := by
  apply (polynomialInheritedSum_le_prime_sum S hD (by linarith only [hs]) le_rfl hz rfl hw).trans
  have hh := mul_le_mul_of_nonneg_left
    (numerical_polynomial_transport_high hD hz2 hw2 hwz rfl hw hs hsσ hK hlocal hlevel)
    (by positivity : 0 ≤ (Real.log (D : ℝ)) ^ (-(5 / 8 : ℝ)))
  simpa only [polynomialCorrection, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh

theorem polynomialInheritedSum_caseII
    {S : BoundingSieve} {D znat : ℕ} {w v s σ K : ℝ}
    (hD : 1 < (D : ℝ)) (hz2 : 2 ≤ (D : ℝ) ^ (1 / s)) (hv2 : 2 ≤ v) (hw2 : 2 ≤ w)
    (hwv : w ≤ v) (hvz : v ≤ (D : ℝ) ^ (1 / s))
    (hz : znat = ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hv : v = (D : ℝ) ^ (1 / (3 : ℝ))) (hw : w = (D : ℝ) ^ (1 / σ))
    (hs : 0 < s) (hσ : 3 ≤ σ)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K)
    (hlevel : 288 * K ^ 2 ≤ Real.log w) :
    polynomialInheritedSum S D znat σ 3 ≤
      (Real.log (D : ℝ)) ^ (-(5 / 8 : ℝ)) / (10 * s) := by
  apply (polynomialInheritedSum_le_prime_sum S hD (by norm_num : (2 : ℝ) ≤ 3) hvz hz hv hw).trans
  have hh := mul_le_mul_of_nonneg_left
    (numerical_polynomial_transport_caseII hD hz2 hv2 hw2 hwv hvz rfl hv hw hs hσ hK hlocal hlevel)
    (by positivity : 0 ≤ (Real.log (D : ℝ)) ^ (-(5 / 8 : ℝ)))
  simpa only [div_eq_mul_inv, mul_one, one_mul] using hh

#print axioms polynomialInheritedSum_high
#print axioms polynomialInheritedSum_caseII
end ChenEffective
