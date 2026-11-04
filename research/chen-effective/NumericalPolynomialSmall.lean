import NumericalPolynomialCompact

/-! A polynomial coefficient for the bounded-level branch of the proposed
mixed-error induction. This is a proved base estimate, not an assumption of
the still separate all-depth mixed-error theorem. -/

namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

noncomputable def polynomialTerminalConstant (A K : ℝ) : ℝ :=
  1792 * (logarithmicR A K) ^ 18 * (logarithmicBudget A) ^ 4

noncomputable def polynomialTerminalScale (S : BoundingSieve) (D K s : ℝ) : ℝ :=
  claim14_5VProduct S D * (Real.exp (Real.sqrt K) / (Real.log D * sourceSigma D 16)) *
    polynomialCorrection D s

theorem numerical_polynomial_terminal_bound (S : BoundingSieve) {K A x : ℝ}
    (hK : 0 < K) (hlocal : HasDimensionOneLocalProductBound S K)
    (n q p : ℕ) (hq : 2 ≤ q) (hp : p = ⌈(q : ℝ) ^ (1 / x)⌉₊)
    (hx : 2 ≤ x) (hA : Real.log (q : ℝ) ≤ A) :
    suzukiActualT S n q p ≤ polynomialTerminalConstant A K * polynomialTerminalScale S q K x := by
  let B := logarithmicBudget A
  let R := logarithmicR A K
  have hB : 1 ≤ B := le_max_left _ _
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hR : 0 < R := by unfold R logarithmicR; positivity
  have hx0 : 0 < x := by linarith only [hx]
  have hL : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hLB : Real.log (q : ℝ) ≤ B := hA.trans (le_max_right _ _)
  have hsigma : 0 < sourceSigma (q : ℝ) 16 := sourceSigma_pos_of_nat_two_le hq
  obtain ⟨hRq, hSig, _⟩ := numerical_logarithmic_bounds hq hK hA
  have hV : 1 / R ≤ claim14_5VProduct S (q : ℝ) := by
    have hRq0 : 0 < (Real.log (q : ℝ) / Real.log 2) * (1 + K / Real.log 2) := by positivity
    have hbase := claim14_5VProduct_lower_of_localProduct (S := S) (D := (q : ℝ)) (K := K)
      (by exact_mod_cast hq) hlocal
    exact (one_div_le_one_div_of_le hRq0 hRq).trans
      ((div_le_iff₀ hRq0).mpr (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hbase))
  have hrest : 1 / (7 * B ^ 3) ≤
      Real.exp (Real.sqrt K) / (Real.log (q : ℝ) * sourceSigma (q : ℝ) 16) := by
    have hden : Real.log (q : ℝ) * sourceSigma (q : ℝ) 16 ≤ 7 * B ^ 3 := by
      have hh := mul_le_mul hLB hSig hsigma.le hB0.le
      nlinarith only [hh]
    exact (one_div_le_one_div_of_le (mul_pos hL hsigma) hden).trans
      (div_le_div_of_nonneg_right (Real.one_le_exp (Real.sqrt_nonneg K)) (by positivity))
  have hlogpow : 1 / B ≤ (Real.log (q : ℝ)) ^ (-(5 / 8 : ℝ)) := by
    have hp := (Real.rpow_le_rpow hL.le hLB (by norm_num : (0 : ℝ) ≤ 5 / 8)).trans
      (Real.rpow_le_self_of_one_le hB (by norm_num : (5 / 8 : ℝ) ≤ 1))
    rw [Real.rpow_neg hL.le, one_div]
    exact (inv_le_inv₀ hB0 (Real.rpow_pos_of_pos hL _)).mpr hp
  have hscale : 1 / (7 * R * B ^ 4 * x ^ 4) ≤ polynomialTerminalScale S q K x := by
    unfold polynomialTerminalScale polynomialCorrection
    calc
      _ = (1 / R) * (1 / (7 * B ^ 3)) * ((1 / B) / x ^ 4) := by field_simp
      _ ≤ _ := by
        have hv0 := (show 0 ≤ 1 / R by positivity).trans hV
        have hr0 := (show 0 ≤ 1 / (7 * B ^ 3) by positivity).trans hrest
        gcongr
  have hc0 : 0 ≤ polynomialTerminalConstant A K := by
    unfold polynomialTerminalConstant
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hscale hc0
  have heq : polynomialTerminalConstant A K * (1 / (7 * R * B ^ 4 * x ^ 4)) =
      256 * R ^ 17 / x ^ 4 := by
    unfold polynomialTerminalConstant
    change 1792 * R ^ 18 * B ^ 4 * (1 / (7 * R * B ^ 4 * x ^ 4)) = _
    field_simp [hR.ne', hB0.ne', hx0.ne']
    ring
  rw [heq] at hscaled
  have htail := numerical_actualT_polynomial_log_bound S hK hlocal n q p hq hp hx hA
  exact ((le_div_iff₀ (pow_pos hx0 4)).mpr (by nlinarith only [htail])).trans hscaled

theorem polynomialTerminalConstant_single_exp_cap {C1 K : ℝ}
    (hC1cap : C1 ≤ Real.exp (10 ^ 40 : ℝ)) (hK : 0 ≤ K) (hKcap : K ≤ (10 ^ 90 : ℝ)) :
    polynomialTerminalConstant (C1 * K ^ (7 : ℝ)) K ≤ Real.exp (10 ^ 44 : ℝ) := by
  let A := C1 * K ^ (7 : ℝ)
  let R := logarithmicR A K
  have hR0 : 0 ≤ R := by unfold R logarithmicR logarithmicBudget; positivity
  have hB0 : 0 ≤ logarithmicBudget A := zero_le_one.trans (le_max_left _ _)
  have hBR : logarithmicBudget A ≤ R := by
    unfold R logarithmicR
    nlinarith only [mul_nonneg hB0 hK, hB0]
  have hcap : R ≤ Real.exp (10 ^ 42 : ℝ) := smallQuotient_single_exp_cap hC1cap hK hKcap
  have hc : (1792 : ℝ) ≤ Real.exp (10 ^ 42 : ℝ) := by
    linarith only [Real.add_one_le_exp (10 ^ 42 : ℝ)]
  unfold polynomialTerminalConstant
  calc
    _ ≤ 1792 * R ^ 18 * R ^ 4 := by gcongr
    _ = 1792 * R ^ 22 := by ring
    _ ≤ Real.exp (10 ^ 42 : ℝ) * (Real.exp (10 ^ 42 : ℝ)) ^ 22 := by gcongr
    _ = Real.exp (23 * (10 ^ 42 : ℝ)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      norm_num
    _ ≤ _ := Real.exp_le_exp.mpr (by norm_num)

#print axioms numerical_polynomial_terminal_bound
#print axioms polynomialTerminalConstant_single_exp_cap
end ChenEffective
