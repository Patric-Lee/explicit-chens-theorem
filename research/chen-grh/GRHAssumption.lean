import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# The single external assumption for the GRH Chen route

This is the exact critical-strip statement exported as `LFunction_eq_zero_re`
by the Alpöge/Claude release of 2026-11-20 (`src/Statements.lean`,
`DirichletLZerosOnLine`). It concerns all Dirichlet characters of all nonzero
moduli, and all heights. We assume the statement instead of importing the
large proof. No numerical prime, sieve, or Chen conclusion is included.

Source statement:
https://github.com/Deicyde/riemann-hypothesis/blob/main/src/Statements.lean
Independent verification record: https://math.mit.edu/~drew/grh/
-/
namespace ChenEffective.GRH

def DirichletGRH : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- Full Dirichlet GRH, used as the sole external axiom by user instruction. -/
axiom alpoge_dirichlet_grh : DirichletGRH

theorem dirichlet_zeros_on_line (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ)
    (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : DirichletCharacter.LFunction χ s = 0) : s.re = 1 / 2 :=
  alpoge_dirichlet_grh q χ s h0 h1 hz

theorem zeta_zeros_on_line (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) : s.re = 1 / 2 := by
  apply dirichlet_zeros_on_line 1 (1 : DirichletCharacter ℂ 1) s h0 h1
  simpa only [DirichletCharacter.LFunction_modOne_eq] using hz

/-- The finite modulus-one input follows at every real height. -/
theorem zeta_finite_RH (T : ℝ) :
    ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2 := by
  intro s hz h0 h1 _
  exact zeta_zeros_on_line s h0 h1 hz

theorem dirichlet_nonzero_right_in_strip (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hhalf : (1 / 2 : ℝ) < s.re) (h1 : s.re < 1) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  intro hz
  have h := dirichlet_zeros_on_line q χ s (by linarith) h1 hz
  linarith

#print axioms zeta_finite_RH
#print axioms dirichlet_nonzero_right_in_strip
end ChenEffective.GRH
