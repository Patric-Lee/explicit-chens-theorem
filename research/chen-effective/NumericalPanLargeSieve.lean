import MathlibNt.AnalyticNumberTheory.LargeSieve.FixedPrimitiveSquareMean

open Classical Complex Finset Set
open scoped BigOperators ArithmeticFunction Topology
namespace ChenEffective
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

noncomputable def panSharpConstant : ℝ := 2*(8+2*Real.pi)
lemma panSharpConstant_pos : 0 < panSharpConstant := by unfold panSharpConstant; positivity

theorem numerical_primitive_square_real :
    ∀ (a : ℤ → ℝ) (M : ℤ) (N D Q : ℕ), 0 < D →
      (∑ q ∈ Finset.Ioc D Q, (1/(q.totient : ℝ))*
        ∑ χ : PrimitiveCharacter q, ‖chen1973PrimitiveAmplitude a M N q χ‖^2) ≤
      (8+2*Real.pi)*((Q : ℝ)+(N : ℝ)/(D : ℝ))*chen1973CoefficientEnergy a M N := by
  have h2 := chen1973Lemma2_equationTwo_of_fareyEquationFour chen1973FareyEquationFour
  intro a M N D Q hD
  by_cases hDQ : D < Q
  · let K := Nat.log2 ((Q - 1) / D) + 1
    let E : ℕ → ℝ := fun q =>
      ∑ χ : PrimitiveCharacter q,
        ‖chen1973PrimitiveAmplitude a M N q χ‖ ^ 2
    have henergy : 0 ≤ chen1973CoefficientEnergy a M N := by
      unfold chen1973CoefficientEnergy
      positivity
    rw [← sum_chen1973ModulusCell D Q hD
      (fun q => (1 / (q.totient : ℝ)) * E q)]
    calc
      (∑ k ∈ Finset.range K,
          ∑ q ∈ chen1973ModulusCell D Q k,
            (1 / (q.totient : ℝ)) * E q) ≤
        ∑ k ∈ Finset.range K,
          (4 * ((2 ^ k * D : ℕ) : ℝ) +
            Real.pi * (N : ℝ) / ((2 ^ k * D : ℕ) : ℝ)) *
              chen1973CoefficientEnergy a M N := by
        apply Finset.sum_le_sum
        intro k hk
        exact chen1973EquationThree_cell_le h2 a M N D Q k hD
      _ = (∑ k ∈ Finset.range K,
          (4 * ((2 ^ k * D : ℕ) : ℝ) +
            Real.pi * (N : ℝ) / ((2 ^ k * D : ℕ) : ℝ))) *
              chen1973CoefficientEnergy a M N := by
        rw [Finset.sum_mul]
      _ ≤ (8 * (Q : ℝ) + 2 * Real.pi * (N : ℝ) / (D : ℝ)) *
          chen1973CoefficientEnergy a M N := by
        apply mul_le_mul_of_nonneg_right _ henergy
        exact chen1973_dyadic_scalar_sum_le N D Q hD hDQ
      _ ≤ (8 + 2 * Real.pi) * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
          chen1973CoefficientEnergy a M N := by
        apply mul_le_mul_of_nonneg_right _ henergy
        have hid :
            (8 + 2 * Real.pi) * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) =
              (8 * (Q : ℝ) + 2 * Real.pi * (N : ℝ) / (D : ℝ)) +
                (2 * Real.pi * (Q : ℝ) + 8 * ((N : ℝ) / (D : ℝ))) := by ring
        rw [hid]
        exact le_add_of_nonneg_right (add_nonneg (by positivity) (by positivity))
  · have hQD : Q ≤ D := Nat.le_of_not_gt hDQ
    have hempty : Finset.Ioc D Q = ∅ := by
      ext q
      simp
      omega
    rw [hempty]
    simp
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity)


theorem numerical_primitive_square_complex
    (c : ℤ → ℂ) (M : ℤ) (N D Q : ℕ) (hD : 0 < D) :
    (∑ q ∈ Ioc D Q, (1 / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q,
        ‖∑ n ∈ Icc (M + 1) (M + N), c n * χ.1 (n : ZMod q)‖ ^ 2) ≤
      panSharpConstant *
        ((Q : ℝ) + (N : ℝ) / D) *
        ∑ n ∈ Icc (M + 1) (M + N), ‖c n‖ ^ 2 := by
  let C : ℝ := 8 + 2*Real.pi
  change _ ≤ 2 * C * ((Q : ℝ) + (N : ℝ) / D) *
    ∑ n ∈ Icc (M + 1) (M + N), ‖c n‖ ^ 2
  have hC := numerical_primitive_square_real
  let aR : ℤ → ℝ := fun n => (c n).re
  let aI : ℤ → ℝ := fun n => (c n).im
  have hp (q : ℕ) (χ : PrimitiveCharacter q) :
      ‖∑ n ∈ Icc (M + 1) (M + N), c n * χ.1 (n : ZMod q)‖ ^ 2 ≤
        2 * (‖chen1973PrimitiveAmplitude aR M N q χ‖ ^ 2 +
          ‖chen1973PrimitiveAmplitude aI M N q χ‖ ^ 2) := by
    let AR := chen1973PrimitiveAmplitude aR M N q χ
    let AI := chen1973PrimitiveAmplitude aI M N q χ
    have heq : (∑ n ∈ Icc (M + 1) (M + N), c n * χ.1 (n : ZMod q)) =
        AR + I * AI := by
      dsimp [AR, AI, chen1973PrimitiveAmplitude]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [aR, aI]
      calc
        c n * χ.1 (n : ZMod q) =
            (((c n).re : ℂ) + ((c n).im : ℂ) * I) * χ.1 (n : ZMod q) := by
              rw [Complex.re_add_im]
        _ = ((c n).re : ℂ) * χ.1 (n : ZMod q) +
            I * (((c n).im : ℂ) * χ.1 (n : ZMod q)) := by ring
    rw [heq]
    have h := norm_add_le AR (I * AI)
    have hI : ‖I * AI‖ = ‖AI‖ := by simp
    rw [hI] at h
    have hsquare : ‖AR + I * AI‖ ^ 2 ≤ (‖AR‖ + ‖AI‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    dsimp [AR, AI]
    nlinarith [sq_nonneg (‖AR‖ - ‖AI‖)]
  have hR := hC aR M N D Q hD
  have hI := hC aI M N D Q hD
  calc
    _ ≤ ∑ q ∈ Ioc D Q, (1 / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          2 * (‖chen1973PrimitiveAmplitude aR M N q χ‖ ^ 2 +
            ‖chen1973PrimitiveAmplitude aI M N q χ‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun χ hχ => hp q χ) (by positivity)
    _ = 2 * ((∑ q ∈ Ioc D Q, (1 / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q, ‖chen1973PrimitiveAmplitude aR M N q χ‖ ^ 2) +
        (∑ q ∈ Ioc D Q, (1 / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q, ‖chen1973PrimitiveAmplitude aI M N q χ‖ ^ 2)) := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      have hmul (a b : ℝ) : a * (2 * b) = 2 * (a * b) := by ring
      simp_rw [hmul]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (C * ((Q : ℝ) + (N : ℝ) / D) * chen1973CoefficientEnergy aR M N +
        C * ((Q : ℝ) + (N : ℝ) / D) * chen1973CoefficientEnergy aI M N) := by
      gcongr
    _ = 2 * C * ((Q : ℝ) + (N : ℝ) / D) *
        ∑ n ∈ Icc (M + 1) (M + N), ‖c n‖ ^ 2 := by
      unfold chen1973CoefficientEnergy
      rw [show 2 * C * ((Q : ℝ) + (N : ℝ) / D) *
          (∑ n ∈ Icc (M + 1) (M + N), ‖c n‖ ^ 2) =
        2 * (C * ((Q : ℝ) + (N : ℝ) / D) *
          ∑ n ∈ Icc (M + 1) (M + N), ‖c n‖ ^ 2) by ring]
      apply congrArg (fun z : ℝ => 2 * z)
      rw [← mul_add, ← Finset.sum_add_distrib]
      apply congrArg (fun z : ℝ => C * ((Q : ℝ) + (N : ℝ) / D) * z)
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [aR, aI]
      rw [Complex.sq_norm]
      simp only [Complex.normSq_apply, sq_abs]
      ring


#print axioms numerical_primitive_square_complex
end ChenEffective
