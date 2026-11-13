# Source provenance

Locally adapted source from these pinned Apache-2.0 projects:

- PrimeNumberTheoremAnd, commit `127b50e33f6033e2147921167a117af96d9ba4ea`:
  https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/127b50e33f6033e2147921167a117af96d9ba4ea
  General Hadamard factorization, canonical products, growth estimates, and
  specialization to the completed Riemann zeta/xi function.
- lean-lab-preprints, commit `2fdf0dc222e35d60ab0043d4597b68ebc2abe4cb`:
  https://github.com/sthubbar/lean-lab-preprints/tree/2fdf0dc222e35d60ab0043d4597b68ebc2abe4cb
  Explicit-formula, zero-counting, Gamma/digamma, residue, and elementary
  unsmoothing proofs. Its copies of earlier PNT+ modules retain their original
  attribution. Existing repository modules are reused where possible.
- Mathlib v4.35.0, `Mathlib/NumberTheory/LSeries/RiemannZetaLogDeriv.lean`,
  copyright 2026 Terence Tao: the former functional-equation derivative
  backport is now a compatibility import of the identical theorem in pinned
  Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Original headers and attributions are retained in the copied files. Changes
include local import names, compatibility proofs for the existing Mathlib,
removal of unrelated source sections, and numerical arguments specific to the
proved OpenAI Dirichlet theorem. New local arguments are in
`XiMoment`, `ZeroMoment`, `ZeroBridge`, `Unsmoothing`, `Psi1Estimate`, and
`Application`. No upstream theorem is accepted as an axiom.

The repository now uses Lean v4.34.1 and the exact Mathlib revision required
by the vendored OpenAI proof. The active Chen closure and final integration audits passed on
these pins. No new external Lake package names were introduced.
