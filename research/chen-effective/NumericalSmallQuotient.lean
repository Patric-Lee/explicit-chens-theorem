import NumericalLogarithmicScalar
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Equation1410

/-!
# Absolute small-quotient errors

The bounded branch need not divide its discrete tail by a hat minimum.
The entire finite parity sum is bounded by the exponential series, giving a
linear logarithmic budget, uniformly in depth and without a coordinate cutoff.
The recursive sum split below retains the weighted small-quotient mass as a
separate additive error. It does not assert that this mass is already absorbed
by the final Chen error budget.
-/

open scoped Classical BigOperators
namespace ChenEffective
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144Equation1410

set_option maxHeartbeats 1200000

private theorem primeWeight_nonneg (S : BoundingSieve) {p : ℕ}
    (hp : p ∈ S.prodPrimes.primeFactors) : 0 ≤ S.nu p :=
  (S.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hp)
    (Nat.mem_primeFactors.mp hp).2.1).le

/-- Summing the actual factorial majorants costs one exponential, rather than
the two exponentials in the usual factored tail estimate. -/
theorem numerical_actualT_le_exp_sourceL (S : BoundingSieve) {K : ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K) (n D z : ℕ)
    (hz : 2 ≤ z) :
    suzukiActualT S n D z ≤ Real.exp (suzukiSourceL (z : ℝ) K) := by
  let L := suzukiSourceL (z : ℝ) K
  have hL : 0 ≤ L := by
    have hmass := lemmaFourteenOne_localProduct_mass hlocal
      (show (2 : ℝ) ≤ z by exact_mod_cast hz)
    exact (Finset.sum_nonneg (fun p hp =>
      primeWeight_nonneg S (Finset.mem_filter.mp hp).1)).trans hmass
  rw [suzukiActualT_eq_parity_sum]
  calc
    _ ≤ ∑ j ∈ suzukiActualParityCarrier n, L ^ j / (j.factorial : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      exact suzukiLemma14_1_pointwise_of_localProduct S j D z hlocal hz
    _ ≤ ∑' j : ℕ, L ^ j / (j.factorial : ℝ) :=
      (Real.summable_pow_div_factorial L).sum_le_tsum _ (fun j _ => by positivity)
    _ = Real.exp L := by
      have hexp : HasSum (fun j : ℕ => L ^ j / (j.factorial : ℝ)) (Real.exp L) := by
        simpa [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp L
      exact hexp.tsum_eq

/-- A polynomial absolute bound on every bounded logarithmic quotient. This
also covers the odd low strip: no lower bound on a real coordinate is needed. -/
theorem numerical_actualT_absolute_log_bound (S : BoundingSieve) {K A : ℝ}
    (hK : 0 < K) (hlocal : HasDimensionOneLocalProductBound S K)
    (n q p : ℕ) (hq : 2 ≤ q) (hp : 2 ≤ p) (hpq : p ≤ q)
    (hA : Real.log (q : ℝ) ≤ A) :
    suzukiActualT S n q p ≤ logarithmicR A K := by
  have hqlog : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hexp : Real.exp (suzukiSourceL (q : ℝ) K) =
      (Real.log (q : ℝ) / Real.log 2) * (1 + K / Real.log 2) := by
    unfold suzukiSourceL
    rw [Real.exp_add, Real.exp_log (by positivity), Real.exp_log (by positivity)]
  calc
    _ ≤ Real.exp (suzukiSourceL (p : ℝ) K) :=
      numerical_actualT_le_exp_sourceL S hlocal n q p hp
    _ ≤ Real.exp (suzukiSourceL (q : ℝ) K) := by
      apply Real.exp_le_exp.mpr
      exact suzukiSourceL_mono (by exact_mod_cast (show 1 < p by omega))
        (by exact_mod_cast hpq)
    _ = _ := hexp
    _ ≤ _ := (numerical_logarithmic_bounds hq hK hA).1

/-- The unabsorbed terminal mass, with the actual natural ceiling quotient. -/
noncomputable def recursiveSmallMass (S : BoundingSieve) (F : Finset ℕ)
    (D : ℕ) (A : ℝ) : ℝ :=
  ∑ p ∈ F.filter (fun p => Real.log ((D ⌈/⌉ p : ℕ) : ℝ) ≤ A), S.nu p

theorem recursiveSmallMass_nonneg (S : BoundingSieve) (F : Finset ℕ)
    (D : ℕ) (A : ℝ) (hsupport : F ⊆ S.prodPrimes.primeFactors) :
    0 ≤ recursiveSmallMass S F D A := by
  exact Finset.sum_nonneg (fun p hp =>
    primeWeight_nonneg S (hsupport (Finset.mem_filter.mp hp).1))

/-- The terminal carrier itself has only logarithmic prime mass. This estimate
is uniform in the parent level and retains the mass instead of counting primes. -/
theorem recursiveSmallMass_le_log (S : BoundingSieve) {K A : ℝ}
    (hK : 0 < K) (hA : 0 ≤ A) (hlocal : HasDimensionOneLocalProductBound S K)
    (F : Finset ℕ) (D : ℕ) (hsupport : F ⊆ S.prodPrimes.primeFactors)
    (hpq : ∀ p ∈ F, p ≤ D ⌈/⌉ p) :
    recursiveSmallMass S F D A ≤ Real.log (logarithmicR (A + 1) K) := by
  classical
  let z := Real.exp (A + 1)
  have hz : 2 ≤ z := by
    have hh := Real.add_one_le_exp (A + 1)
    dsimp [z]
    linarith only [hh, hA]
  have hsub : F.filter (fun p => Real.log ((D ⌈/⌉ p : ℕ) : ℝ) ≤ A) ⊆
      S.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z) := by
    intro p hp
    obtain ⟨hpF, hpA⟩ := Finset.mem_filter.mp hp
    have hpP := hsupport hpF
    have hp0 : (0 : ℝ) < p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hpP).pos
    have hq0 : (0 : ℝ) < (D ⌈/⌉ p : ℕ) :=
      hp0.trans_le (by exact_mod_cast hpq p hpF)
    have hlogp : Real.log (p : ℝ) ≤ A :=
      (Real.log_le_log hp0 (by exact_mod_cast hpq p hpF)).trans hpA
    have hpz : (p : ℝ) < z := by
      rw [← Real.exp_log hp0]
      exact Real.exp_lt_exp.mpr (by linarith only [hlogp])
    exact Finset.mem_filter.mpr ⟨hpP, hpz⟩
  have hmass : recursiveSmallMass S F D A ≤ suzukiSourceL z K := by
    apply le_trans _ (lemmaFourteenOne_localProduct_mass hlocal hz)
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p hp _ => primeWeight_nonneg S (Finset.mem_filter.mp hp).1)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hinv : (Real.log (2 : ℝ))⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀' hlog2]
    linarith only [Real.log_two_gt_d9]
  have hleft : (A + 1) / Real.log 2 ≤ 2 * (A + 1) := by
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_right hinv (show 0 ≤ A + 1 by linarith)
  have hright : K / Real.log 2 ≤ 2 * K := by
    simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_right hinv hK.le
  have hprod : (A + 1) / Real.log 2 * (1 + K / Real.log 2) ≤
      logarithmicR (A + 1) K := by
    unfold logarithmicR logarithmicBudget
    rw [max_eq_right (show 1 ≤ A + 1 by linarith)]
    exact mul_le_mul hleft (by linarith only [hright]) (by positivity) (by positivity)
  apply hmass.trans
  unfold suzukiSourceL
  rw [show Real.log z = A + 1 by exact Real.log_exp _]
  rw [← Real.log_mul (by positivity : (A + 1) / Real.log 2 ≠ 0)
    (by positivity : 1 + K / Real.log 2 ≠ 0)]
  exact Real.log_le_log (by positivity) hprod

/-- The full immediate terminal contribution, without a hat denominator. -/
theorem numerical_small_quotient_sum_bound (S : BoundingSieve) {K A : ℝ}
    (hK : 0 < K) (hA : 0 ≤ A) (hlocal : HasDimensionOneLocalProductBound S K)
    (F : Finset ℕ) (n D : ℕ) (hsupport : F ⊆ S.prodPrimes.primeFactors)
    (hpoints : ∀ p ∈ F, 2 ≤ D ⌈/⌉ p ∧ 2 ≤ p ∧ p ≤ D ⌈/⌉ p) :
    (∑ p ∈ F.filter (fun p => Real.log ((D ⌈/⌉ p : ℕ) : ℝ) ≤ A),
      S.nu p * suzukiActualT S n (D ⌈/⌉ p) p) ≤
      logarithmicR A K * Real.log (logarithmicR (A + 1) K) := by
  calc
    _ ≤ logarithmicR A K * recursiveSmallMass S F D A := by
      rw [recursiveSmallMass, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpF, hsmall⟩ := Finset.mem_filter.mp hp
      have hb := numerical_actualT_absolute_log_bound S hK hlocal n (D ⌈/⌉ p) p
        (hpoints p hpF).1 (hpoints p hpF).2.1 (hpoints p hpF).2.2 hsmall
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left hb (primeWeight_nonneg S (hsupport hpF))
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (recursiveSmallMass_le_log S hK hA hlocal F D hsupport
        (fun p hp => (hpoints p hp).2.2)) (by unfold logarithmicR logarithmicBudget; positivity)

/-- Equation-(14.10) style transport with a separate absolute terminal error.
The large-quotient hypothesis is the induction input; the small-quotient bound
is proved here from the local product bound, uniformly in the depth. -/
theorem numerical_recursive_sum_split (S : BoundingSieve) {K A : ℝ}
    (hK : 0 < K) (hlocal : HasDimensionOneLocalProductBound S K)
    (F : Finset ℕ) (n D : ℕ) (main error : ℕ → ℝ)
    (hsupport : F ⊆ S.prodPrimes.primeFactors)
    (hpoints : ∀ p ∈ F, 2 ≤ D ⌈/⌉ p ∧ 2 ≤ p ∧ p ≤ D ⌈/⌉ p)
    (hmain : ∀ p ∈ F, Real.log ((D ⌈/⌉ p : ℕ) : ℝ) ≤ A → 0 ≤ main p)
    (hlarge : ∀ p ∈ F, A < Real.log ((D ⌈/⌉ p : ℕ) : ℝ) →
      suzukiActualT S n (D ⌈/⌉ p) p ≤ main p + error p) :
    (∑ p ∈ F, S.nu p * suzukiActualT S n (D ⌈/⌉ p) p) ≤
      (∑ p ∈ F, S.nu p * main p) +
      (∑ p ∈ F.filter (fun p => A < Real.log ((D ⌈/⌉ p : ℕ) : ℝ)),
        S.nu p * error p) +
      logarithmicR A K * recursiveSmallMass S F D A := by
  classical
  rw [recursiveSmallMass, Finset.mul_sum]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  by_cases hsmall : Real.log ((D ⌈/⌉ p : ℕ) : ℝ) ≤ A
  · have hb := numerical_actualT_absolute_log_bound S hK hlocal n (D ⌈/⌉ p) p
      (hpoints p hp).1 (hpoints p hp).2.1 (hpoints p hp).2.2 hsmall
    have hm := mul_nonneg (primeWeight_nonneg S (hsupport hp)) (hmain p hp hsmall)
    have hw := mul_le_mul_of_nonneg_left hb (primeWeight_nonneg S (hsupport hp))
    simp only [hsmall, not_lt_of_ge hsmall, ite_true, ite_false]
    nlinarith only [hm, hw]
  · have hb := mul_le_mul_of_nonneg_left (hlarge p hp (lt_of_not_ge hsmall))
      (primeWeight_nonneg S (hsupport hp))
    simp only [hsmall, lt_of_not_ge hsmall, ite_true, ite_false, add_zero]
    simpa only [mul_add] using hb

/-- The additive induction step with a completely explicit terminal
coefficient. Only the large-quotient estimates remain induction inputs. -/
theorem numerical_recursive_sum_split_absolute (S : BoundingSieve) {K A : ℝ}
    (hK : 0 < K) (hA : 0 ≤ A) (hlocal : HasDimensionOneLocalProductBound S K)
    (F : Finset ℕ) (n D : ℕ) (main error : ℕ → ℝ)
    (hsupport : F ⊆ S.prodPrimes.primeFactors)
    (hpoints : ∀ p ∈ F, 2 ≤ D ⌈/⌉ p ∧ 2 ≤ p ∧ p ≤ D ⌈/⌉ p)
    (hmain : ∀ p ∈ F, Real.log ((D ⌈/⌉ p : ℕ) : ℝ) ≤ A → 0 ≤ main p)
    (hlarge : ∀ p ∈ F, A < Real.log ((D ⌈/⌉ p : ℕ) : ℝ) →
      suzukiActualT S n (D ⌈/⌉ p) p ≤ main p + error p) :
    (∑ p ∈ F, S.nu p * suzukiActualT S n (D ⌈/⌉ p) p) ≤
      (∑ p ∈ F, S.nu p * main p) +
      (∑ p ∈ F.filter (fun p => A < Real.log ((D ⌈/⌉ p : ℕ) : ℝ)),
        S.nu p * error p) +
      logarithmicR A K * Real.log (logarithmicR (A + 1) K) := by
  apply (numerical_recursive_sum_split S hK hlocal F n D main error
    hsupport hpoints hmain hlarge).trans
  have hh : logarithmicR A K * recursiveSmallMass S F D A ≤
      logarithmicR A K * Real.log (logarithmicR (A + 1) K) := mul_le_mul_of_nonneg_left
    (recursiveSmallMass_le_log S hK hA hlocal F D hsupport
      (fun p hp => (hpoints p hp).2.2))
    (by unfold logarithmicR logarithmicBudget; positivity)
  exact add_le_add le_rfl hh

/-- Each recursive step loses at most a factor two in the logarithmic level
when the prime is at most the parent's square root. -/
theorem recursive_log_half {D p : ℕ} (hp : 2 ≤ p) (hpsq : p ^ 2 ≤ D) :
    Real.log (D : ℝ) ≤ 2 * Real.log ((D ⌈/⌉ p : ℕ) : ℝ) := by
  have hp0 : 0 < p := by omega
  have hDmul := (ceilDiv_le_iff_le_mul hp0).mp (le_refl (D ⌈/⌉ p))
  have hpq : p ≤ D ⌈/⌉ p := by
    by_contra h
    have hlt : D ⌈/⌉ p < p := lt_of_not_ge h
    nlinarith only [hDmul, hpsq, hlt]
  have hq0 : (0 : ℝ) < (D ⌈/⌉ p : ℕ) := by
    exact_mod_cast (show 0 < D ⌈/⌉ p by omega)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by nlinarith)
  have hDsq : (D : ℝ) ≤ ((D ⌈/⌉ p : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast (show D ≤ (D ⌈/⌉ p) ^ 2 by nlinarith only [hDmul, hpq])
  calc
    _ ≤ Real.log (((D ⌈/⌉ p : ℕ) : ℝ) ^ 2) := Real.log_le_log hD0 hDsq
    _ = _ := by rw [Real.log_pow]; norm_num

/-- Above twice the boundary logarithm, there is no terminal mass in the
immediate recursive sum. This does not rule out terminals at later depths. -/
theorem recursiveSmallMass_eq_zero (S : BoundingSieve) (F : Finset ℕ)
    {D : ℕ} {A : ℝ} (hlarge : 2 * A < Real.log (D : ℝ))
    (hpoints : ∀ p ∈ F, 2 ≤ p ∧ p ^ 2 ≤ D) :
    recursiveSmallMass S F D A = 0 := by
  classical
  unfold recursiveSmallMass
  have hf : F.filter (fun p => Real.log ((D ⌈/⌉ p : ℕ) : ℝ) ≤ A) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro p hp hsmall
    have hh := recursive_log_half (hpoints p hp).1 (hpoints p hp).2
    linarith only [hh, hlarge, hsmall]
  rw [hf, Finset.sum_empty]

/-- The terminal coefficient has a single-exponential cap even when the
separator has the current single-exponential C1 bound. -/
theorem smallQuotient_single_exp_cap {C1 K : ℝ}
    (hC1cap : C1 ≤ Real.exp (10 ^ 40 : ℝ))
    (hK : 0 ≤ K) (hKcap : K ≤ (10 ^ 90 : ℝ)) :
    logarithmicR (C1 * K ^ (7 : ℝ)) K ≤ Real.exp (10 ^ 42 : ℝ) := by
  have he1 : (1 : ℝ) ≤ Real.exp (1000 : ℝ) := Real.one_le_exp (by positivity)
  have hKE : K ≤ Real.exp (1000 : ℝ) := by
    have hten : (10 : ℝ) ≤ Real.exp 10 := by
      linarith only [Real.add_one_le_exp (10 : ℝ)]
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) hten 90
    rw [← Real.exp_nat_mul] at hh
    exact hKcap.trans (hh.trans (Real.exp_le_exp.mpr (by norm_num)))
  have hpow : K ^ (7 : ℝ) ≤ Real.exp (7 * (1000 : ℝ)) := by
    rw [show (7 : ℝ) = (7 : ℕ) by norm_num, Real.rpow_natCast,
      Real.exp_nat_mul]
    exact pow_le_pow_left₀ hK hKE 7
  have hA : C1 * K ^ (7 : ℝ) ≤ Real.exp (10 ^ 41 : ℝ) := by
    calc
      _ ≤ Real.exp (10 ^ 40 : ℝ) * Real.exp (7 * (1000 : ℝ)) :=
        mul_le_mul hC1cap hpow (Real.rpow_nonneg hK _) (Real.exp_pos _).le
      _ = Real.exp ((10 ^ 40 : ℝ) + 7 * 1000) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by norm_num)
  have hB : logarithmicBudget (C1 * K ^ (7 : ℝ)) ≤ Real.exp (10 ^ 41 : ℝ) :=
    max_le (Real.one_le_exp (by positivity)) hA
  have hfactor : 1 + 2 * K ≤ Real.exp (2 * (1000 : ℝ)) := by
    have h3 : (3 : ℝ) ≤ Real.exp (1000 : ℝ) := by
      linarith only [Real.add_one_le_exp (1000 : ℝ)]
    calc
      _ ≤ 3 * Real.exp (1000 : ℝ) := by linarith only [hKE, he1]
      _ ≤ Real.exp (1000 : ℝ) * Real.exp (1000 : ℝ) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have htwo : (2 : ℝ) ≤ Real.exp (1000 : ℝ) := by linarith only [Real.add_one_le_exp (1000 : ℝ)]
  unfold logarithmicR
  have hB0 : 0 ≤ logarithmicBudget (C1 * K ^ (7 : ℝ)) :=
    zero_le_one.trans (le_max_left _ _)
  calc
    _ ≤ Real.exp (1000 : ℝ) * Real.exp (10 ^ 41 : ℝ) *
        Real.exp (2 * (1000 : ℝ)) := by
      gcongr
    _ = Real.exp ((1000 : ℝ) + 10 ^ 41 + 2 * 1000) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by norm_num)

/-- A uniform cap for the entire immediate terminal sum, still with a single
exponential rather than a reciprocal compact-hat minimum. -/
theorem smallQuotient_terminal_single_exp_cap {C1 K : ℝ}
    (hC1 : 0 ≤ C1) (hC1cap : C1 ≤ Real.exp (10 ^ 40 : ℝ))
    (hK : 0 ≤ K) (hKcap : K ≤ (10 ^ 90 : ℝ)) :
    logarithmicR (C1 * K ^ (7 : ℝ)) K *
      Real.log (logarithmicR (C1 * K ^ (7 : ℝ) + 1) K) ≤
        Real.exp (10 ^ 43 : ℝ) := by
  let A := C1 * K ^ (7 : ℝ)
  have hA : 0 ≤ A := mul_nonneg hC1 (Real.rpow_nonneg hK _)
  have hB0 : 0 < logarithmicBudget A := zero_lt_one.trans_le (le_max_left _ _)
  have hR0 : 0 < logarithmicR A K := by unfold logarithmicR; positivity
  have hR1 : 0 < logarithmicR (A + 1) K := by
    unfold logarithmicR logarithmicBudget
    positivity
  have hbudget : logarithmicBudget (A + 1) ≤ 2 * logarithmicBudget A := by
    unfold logarithmicBudget
    have h1 := le_max_left (1 : ℝ) A
    have h2 := le_max_right (1 : ℝ) A
    rw [max_eq_right (by linarith only [hA])]
    linarith only [h1, h2]
  have hR : logarithmicR (A + 1) K ≤ 2 * logarithmicR A K := by
    unfold logarithmicR
    nlinarith only [mul_le_mul_of_nonneg_right hbudget
      (show 0 ≤ 1 + 2 * K by positivity)]
  have hlog : Real.log (logarithmicR (A + 1) K) ≤ 2 * logarithmicR A K :=
    ((Real.log_le_sub_one_of_pos hR1).trans (by linarith)).trans hR
  have hcap := smallQuotient_single_exp_cap hC1cap hK hKcap
  have he2 : (2 : ℝ) ≤ Real.exp (10 ^ 42 : ℝ) := by
    linarith only [Real.add_one_le_exp (10 ^ 42 : ℝ)]
  calc
    _ ≤ 2 * (logarithmicR A K) ^ 2 := by
      nlinarith only [mul_le_mul_of_nonneg_left hlog hR0.le]
    _ ≤ Real.exp (10 ^ 42 : ℝ) * (Real.exp (10 ^ 42 : ℝ)) ^ 2 := by
      gcongr
    _ = Real.exp (3 * (10 ^ 42 : ℝ)) := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by norm_num)

#print axioms numerical_actualT_absolute_log_bound
#print axioms numerical_recursive_sum_split
#print axioms numerical_small_quotient_sum_bound
#print axioms recursiveSmallMass_eq_zero
#print axioms smallQuotient_single_exp_cap
#print axioms smallQuotient_terminal_single_exp_cap
end ChenEffective
