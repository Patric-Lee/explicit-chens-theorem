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
  copyright 2026 Terence Tao: the functional-equation derivative is backported
  locally in `DusartPort/ZetaLogDeriv.lean`.

Original headers and attributions are retained in the copied files. Changes
include local import names, compatibility proofs for the existing Mathlib,
removal of unrelated source sections, and numerical arguments specific to the
single permitted Dirichlet hypothesis. New local arguments are in
`XiMoment`, `ZeroMoment`, `ZeroBridge`, `Unsmoothing`, `Psi1Estimate`, and
`Application`. No upstream theorem is accepted as an axiom.

All files are checked against the repository's existing Lean v4.33.0-rc1;
neither upstream toolchains nor upstream Lake dependencies are installed.
