import NumericalLogarithmicScalar
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseABoundedK

open scoped Classical BigOperators
open Filter Finset MeasureTheory Set Topology Real
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The envelope needs a budget for log(q), rather than for q itself. -/
noncomputable def quotientLogBudget (q : ℕ) : ℕ := ⌈Real.log (q : ℝ)⌉₊

theorem quotientLogBudget_covers (q : ℕ) : Real.log (q : ℝ) ≤ quotientLogBudget q :=
  Nat.le_ceil _

theorem quotientLogBudget_le {q : ℕ} {A : ℝ} (h : Real.log (q : ℝ) ≤ A) :
    quotientLogBudget q ≤ ⌈A⌉₊ := Nat.ceil_mono h

/-- In the bounded branch, the compact hat coordinate is linear in the
logarithmic budget A, instead of exponential in A. -/
theorem quotientHatCutoff_log_budget {q : ℕ} {A : ℝ} (hq : 2 ≤ q)
    (h : Real.log (q : ℝ) ≤ A) :
    (quotientCoordinateCutoff (quotientLogBudget q) : ℝ) ≤ 1679616*(A+1)+6 := by
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hA : 0 ≤ A := hlog.le.trans h
  have hqA : (quotientLogBudget q : ℝ) ≤ (⌈A⌉₊ : ℝ) := by exact_mod_cast quotientLogBudget_le h
  have hc := Nat.ceil_lt_add_one hA
  simp only [quotientCoordinateCutoff,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  linarith only [hqA,hc]

noncomputable def fixedQuotientScalarConstant (q : ℕ) (K : ℝ) : ℝ :=
  let L := Real.log (q : ℝ)
  let R := (L / Real.log 2) * (1 + K / Real.log 2)
  Real.exp (2 * suzukiSourceL (q : ℝ) K) /
    ((1 / R) * (Real.exp (Real.sqrt K) / (L * sourceSigma (q : ℝ) 16)) *
      quotientEnvelopeLower (quotientLogBudget q) * L ^ (-(1 / 2 : ℝ)))

/-- The fixed-quotient scalar has a displayed coefficient, with no hat minima. -/
theorem numerical_fixed_quotient_scalar
    (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    {q : ℕ} (hq : 2 ≤ q) {K : ℝ} (hK : 0 < K) :
    0 < fixedQuotientScalarConstant q K ∧ ∀ (S : BoundingSieve),
      HasDimensionOneLocalProductBound S K → ∀ (n p : ℕ) (x : ℝ),
      p = ⌈(q : ℝ) ^ (1 / x)⌉₊ → 2 ≤ x →
      suzukiSourceL (p : ℝ) K ^ (⌊x - 2⌋₊ + 1) /
          ((⌊x - 2⌋₊ + 1).factorial : ℝ) * Real.exp (suzukiSourceL (p : ℝ) K) ≤
        fixedQuotientScalarConstant q K * claim14_5Scale S H n (q : ℝ) 16 (1 / 2)
          (sourceSigma (q : ℝ) 16) K x := by
  let d : ℝ := 16
  let Δ : ℝ := 1 / 2
  let e0 := quotientEnvelopeLower (quotientLogBudget q)
  have he0 : 0 < e0 := quotientEnvelopeLower_pos (quotientLogBudget q)
  have hEnvelopeLower (n : ℕ) (x : ℝ) (hx : 2 ≤ x) :
      e0 ≤ errorEnvelope H n (q : ℝ) d x := by
    exact numerical_error_envelope_lower hH.toSection13HatContract hq (quotientLogBudget_covers q) n hx
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hsigma : 0 < sourceSigma (q : ℝ) d := sourceSigma_pos_of_nat_two_le hq
  let Rq : ℝ := (Real.log (q : ℝ) / Real.log 2) * (1 + K / Real.log 2)
  have hRq : 0 < Rq := by dsimp [Rq]; positivity
  let B0 : ℝ := (1 / Rq) *
      (Real.exp (Real.sqrt K) / (Real.log (q : ℝ) * sourceSigma (q : ℝ) d)) *
      e0 * (Real.log (q : ℝ)) ^ (-Δ)
  have hB0 : 0 < B0 := by dsimp [B0]; positivity
  let Lq : ℝ := suzukiSourceL (q : ℝ) K
  let A : ℝ := Real.exp (2 * Lq) / B0
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨hA, ?_⟩
  intro S hlocal n p x hp hx
  have hx0 : 0 < x := by linarith
  have hpq : p ≤ q := by rw [hp]; exact claim145_natCeil_rpow_le hq hx
  have hp2 : 2 ≤ p := by
    rw [hp]
    have hpow : (1 : ℝ) < (q : ℝ) ^ (1 / x) :=
      Real.one_lt_rpow hq1 (one_div_pos.mpr hx0)
    have : 1 < ⌈(q : ℝ) ^ (1 / x)⌉₊ := (Nat.lt_ceil).mpr (by simpa using hpow)
    omega
  let Lp : ℝ := suzukiSourceL (p : ℝ) K
  have hLp : 0 < Lp := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogp : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.strictMonoOn_log.monotoneOn (by norm_num)
        (show (0 : ℝ) < (p : ℝ) by exact_mod_cast (show 0 < p by omega))
        (by exact_mod_cast hp2)
    have hfirst : 0 ≤ Real.log (Real.log (p : ℝ) / Real.log 2) :=
      Real.log_nonneg ((le_div_iff₀ hlog2).2 (by simpa using hlogp))
    have hsecond : 0 < Real.log (1 + K / Real.log 2) := by
      apply Real.log_pos
      have : 0 < K / Real.log 2 := div_pos hK hlog2
      linarith
    dsimp [Lp, suzukiSourceL]
    linarith
  have hLpq : Lp ≤ Lq := by
    dsimp [Lp, Lq]
    exact suzukiSourceL_mono (by exact_mod_cast (show 1 < p by omega))
      (by exact_mod_cast hpq)
  have hleft :
      Lp ^ (⌊x - 2⌋₊ + 1) / (((⌊x - 2⌋₊ + 1).factorial : ℕ) : ℝ) *
          Real.exp Lp ≤ Real.exp (2 * Lq) := by
    have hterm := Real.pow_div_factorial_le_exp Lp hLp.le (⌊x - 2⌋₊ + 1)
    calc
      _ ≤ Real.exp Lp * Real.exp Lp :=
        mul_le_mul_of_nonneg_right hterm (Real.exp_pos Lp).le
      _ = Real.exp (2 * Lp) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (2 * Lq) := Real.exp_le_exp.mpr (by linarith)
  have hEnvelope : e0 ≤ errorEnvelope H n (q : ℝ) d x :=
    hEnvelopeLower n x hx
  have hVlower : 1 / Rq ≤ claim14_5VProduct S (q : ℝ) := by
    apply (div_le_iff₀ hRq).2
    simpa [Rq, mul_comm, mul_left_comm, mul_assoc] using
      (claim14_5VProduct_lower_of_localProduct
        (S := S) (D := (q : ℝ)) (K := K) (by exact_mod_cast hq) hlocal)
  have hscale : B0 ≤ claim14_5Scale S H n (q : ℝ) d Δ
      (sourceSigma (q : ℝ) d) K x := by
    unfold claim14_5Scale
    dsimp [B0]
    have hrest : 0 ≤ Real.exp (Real.sqrt K) /
        (Real.log (q : ℝ) * sourceSigma (q : ℝ) d) := by positivity
    have htail : 0 ≤ (Real.log (q : ℝ)) ^ (-Δ) := Real.rpow_nonneg hlogq.le _
    have hV0 : 0 ≤ claim14_5VProduct S (q : ℝ) :=
      (show 0 ≤ 1 / Rq by positivity).trans hVlower
    calc
      (1 / Rq) * (Real.exp (Real.sqrt K) /
          (Real.log (q : ℝ) * sourceSigma (q : ℝ) d)) * e0 *
          (Real.log (q : ℝ)) ^ (-Δ) ≤
        claim14_5VProduct S (q : ℝ) *
          (Real.exp (Real.sqrt K) /
            (Real.log (q : ℝ) * sourceSigma (q : ℝ) d)) * e0 *
          (Real.log (q : ℝ)) ^ (-Δ) := by gcongr
      _ ≤ claim14_5VProduct S (q : ℝ) *
          (Real.exp (Real.sqrt K) /
            (Real.log (q : ℝ) * sourceSigma (q : ℝ) d)) *
          errorEnvelope H n (q : ℝ) d x *
          (Real.log (q : ℝ)) ^ (-Δ) := by gcongr
  calc
    _ ≤ Real.exp (2 * Lq) := by simpa [Lp] using hleft
    _ = A * B0 := by dsimp [A]; field_simp [ne_of_gt hB0]
    _ ≤ A * claim14_5Scale S H n (q : ℝ) d Δ
        (sourceSigma (q : ℝ) d) K x := mul_le_mul_of_nonneg_left hscale hA.le



noncomputable def fixedDScalarConstant (Dmin : ℕ) (K : ℝ) : ℝ :=
  1 + ∑ q ∈ Finset.Ico 2 Dmin, fixedQuotientScalarConstant q K

/-- A displayed finite arithmetic sum replaces the old chosen fixed-q coefficients. -/
theorem numerical_fixedD_scalar
    (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    (Dmin : ℕ) {K C1 : ℝ} (hK : 0 < K)
    (hCaseA_lt : ∀ q : ℕ, 2 ≤ q → Real.log (q : ℝ) ≤ C1 * K ^ (7 : ℝ) → q < Dmin) :
    0 < fixedDScalarConstant Dmin K ∧ ∀ S : BoundingSieve,
      HasDimensionOneLocalProductBound S K →
      Claim145SmallDCaseAScalarComparison S H 16 (1 / 2) (fixedDScalarConstant Dmin K) K C1 7 := by
  let d : ℝ := 16
  let Δ : ℝ := 1 / 2
  let Aq := fun q : ℕ => fixedQuotientScalarConstant q K
  have hAq_pos (q : ℕ) (hq : 2 ≤ q) : 0 < Aq q :=
    (numerical_fixed_quotient_scalar H hH hq hK).1
  have hAq_bound (q : ℕ) (hq : 2 ≤ q) :=
    (numerical_fixed_quotient_scalar H hH hq hK).2
  let C145 : ℝ := 1 + ∑ q ∈ Finset.Ico 2 Dmin, Aq q
  have hsum0 : 0 ≤ ∑ q ∈ Finset.Ico 2 Dmin, Aq q := by
    apply Finset.sum_nonneg
    intro q hq
    exact (hAq_pos q (Finset.mem_Ico.mp hq).1).le
  have hC145 : 0 < C145 := by dsimp [C145]; linarith
  refine ⟨hC145, ?_⟩
  intro S hlocal n q p x hq hp hx hsmall
  have hqD : q < Dmin := hCaseA_lt q hq hsmall
  have hterm : Aq q ≤ ∑ a ∈ Finset.Ico 2 Dmin, Aq a := by
    apply Finset.single_le_sum
    · intro a ha
      exact (hAq_pos a (Finset.mem_Ico.mp ha).1).le
    · simp [hq, hqD]
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hscale0 : 0 ≤ claim14_5Scale S H n (q : ℝ) d Δ
      (sourceSigma (q : ℝ) d) K x := by
    have hx0 : 0 < x := by linarith
    have hsigma : 0 < sourceSigma (q : ℝ) d := sourceSigma_pos_of_nat_two_le hq
    have hE : 0 ≤ errorEnvelope H n (q : ℝ) d x :=
      errorEnvelope_nonneg H n hq1 hx0.le
        (hH.toSection13HatContract.positive _ x hx0).le
    unfold claim14_5Scale
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (suzukiVProduct_pos S (q : ℝ)).le
          (div_nonneg (Real.exp_pos _).le (mul_pos hlogq hsigma).le)) hE)
      (Real.rpow_nonneg hlogq.le _)
  exact (hAq_bound q hq S hlocal n p x hp hx).trans
    (mul_le_mul_of_nonneg_right (by
      change Aq q ≤ 1 + ∑ a ∈ Finset.Ico 2 Dmin, Aq a
      linarith only [hterm]) hscale0)


noncomputable def boundedCaseAConstant (C1 Kmax : ℝ) : ℝ :=
  logarithmicScalarConstant (C1 * Kmax ^ (7 : ℝ)) Kmax * Real.exp (Real.sqrt Kmax)

/-- Fully explicit coefficient for the bounded-K branch, as a function of its two inputs. -/
theorem numerical_caseA_boundedK
    (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    {C1 Kmax : ℝ} (hC1 : 0 ≤ C1) (hKmax : 1 ≤ Kmax) :
    0 < boundedCaseAConstant C1 Kmax ∧
      ∀ (S : BoundingSieve) (N D z : ℕ) (K s : ℝ),
        1 ≤ K → K ≤ Kmax → HasDimensionOneLocalProductBound S K →
        2 ≤ D → z = ⌈(D : ℝ) ^ (1 / s)⌉₊ → 2 ≤ s →
        Real.log (D : ℝ) ≤ C1 * K ^ (7 : ℝ) →
        Claim14_5Bound (fun m D' z' => suzukiActualT S m ⌈D'⌉₊ ⌈z'⌉₊)
          S H N (D : ℝ) (z : ℝ) 16 (1 / 2)
          (sourceSigma (D : ℝ) 16) K s (boundedCaseAConstant C1 Kmax) := by
  let d : ℝ := 16
  let Δ : ℝ := 1 / 2
  let Θ : ℝ := 7
  have hΘ : 0 ≤ Θ := by norm_num [Θ]
  let A : ℝ := C1 * Kmax ^ Θ
  have hKmax0 : 0 < Kmax := lt_of_lt_of_le zero_lt_one hKmax
  let C0 := logarithmicScalarConstant A Kmax
  have hC0 : 0 < C0 := logarithmicScalarConstant_pos hKmax0
  let C145 : ℝ := C0 * Real.exp (Real.sqrt Kmax)
  have hC145 : 0 < C145 := by dsimp [C145]; positivity
  refine ⟨hC145, ?_⟩
  intro S N D z K s hK hKK hlocal hD hz hs hsmall
  have hlocal' := hasDimensionOneLocalProductBound_mono_K hlocal hKK
  have hpow : K ^ Θ ≤ Kmax ^ Θ :=
    Real.rpow_le_rpow (by linarith) hKK hΘ
  have hsmall' : Real.log (D : ℝ) ≤ C1 * Kmax ^ Θ :=
    hsmall.trans (mul_le_mul_of_nonneg_left hpow hC1)
  have htail := suzukiLemma14_3_natCeil_uniform_explicit
    (S := S) (N := N) (D := D) (z := z) (s := s) (K := Kmax)
    hlocal' (by omega) hs hz
  have hscalar' := numerical_uniform_log_scalar H hH hKmax0 S hlocal' N D z s hD hz hs hsmall'
  have hupper : suzukiActualT S N D z ≤
      C0 * claim14_5Scale S H N (D : ℝ) d Δ
        (sourceSigma (D : ℝ) d) Kmax s := htail.trans hscalar'
  have hscale := claim14_5Scale_upperK_le S H N
    (D := (D : ℝ)) (d := d) (Δ := Δ)
    (σ := sourceSigma (D : ℝ) d) (K := K) (Kmax := Kmax) (s := s)
    (by exact_mod_cast (show 1 < D by omega))
    (sourceSigma_pos_of_nat_two_le hD) (by linarith)
    (hH.toSection13HatContract.positive _ s (by linarith)).le
  have hfinal : suzukiActualT S N D z ≤
      C145 * claim14_5Scale S H N (D : ℝ) d Δ
        (sourceSigma (D : ℝ) d) K s := hupper.trans (by
    dsimp [C145]
    nlinarith [mul_le_mul_of_nonneg_left hscale hC0.le])
  simpa [Claim14_5Bound, d, Δ, C145, C0, A, Θ, boundedCaseAConstant] using hfinal



#print axioms numerical_fixed_quotient_scalar
#print axioms numerical_fixedD_scalar
#print axioms numerical_caseA_boundedK
end ChenEffective
