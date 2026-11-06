# Dusart input: the required blocker is closed

The local package `research/chen-dusart` proves, for x>=3^120,

    abs(theta(x)-x) <= (3/4)*x^(15/16)
    abs(theta(x)-x) <= 4*x/log(x)^2
    abs(P(floor(x))-log(log(x))-M) <= 1/(2*log(x)^2).

It proves the corresponding ordered, closed-left reciprocal-prime interval
bound, including the exact endpoint 3^120. These are theorem conclusions,
not hypotheses, and the only nonstandard axiom is the existing local
Dirichlet seven-eighths hypothesis.

## How the middle range was resolved

The proof uses xi Hadamard factorization and its positive zero-moment identity.
A numerical bound Re(Lambda_0(0))<=0.03 follows from a 64-term rational harmonic
bound and elementary logarithm bounds. The Dirichlet zero strip, a factor-two
kernel comparison, and an explicit multiplicity-preserving map prove

    sum over zeta zeros of m(rho)/abs(rho*(rho+1)) <= 3/25.

The smoothed explicit formula, including the trivial-zero terms, then gives
abs(psi1(x)-x^2/2)<=0.121*x^(15/8) for x>=3^100. Numerical unsmoothing gives
abs(psi(x)-x)<=0.7*x^(15/16) for x>=3^120. The prime-power correction gives
the theta bound and Abel summation gives the signed prefix bound.

This replaces Dusart's numerical-table route for the restricted estimate
needed here. It is not a formalization of his unconditional Theorem 5.2
with its full small-x range or sharper coefficients. The earlier missing
range 3^120<=x<exp(3400) is now covered by the proved power-saving estimate.
The previous far-tail and Abel lemmas remain valid supporting results.

## Provenance and audits

The local analytic foundations are selectively backported from pinned PNT+
and lean-lab-preprints source, plus one Mathlib functional-equation derivative.
See `research/chen-dusart/NOTICE.md` and `LICENSE-APACHE`. All local source is
compiled against the existing Lean v4.33.0-rc1 and Mathlib. No package
requirements or toolchain versions are changed; no OpenAI modules are imported.

The package's transitive audit checks the numerical results against exactly
propext, Classical.choice, Quot.sound and dirichlet_seven_eighths. Source
scans prohibit local axioms, placeholders, native_decide and unsafe code.

## Propagation

The active BJS product proof now starts at U=3^120, uses the actual prime
interval theorem and pays the prime-square correction. The same lower and
triple inequalities therefore hold at N0=3^(3^171), H approximately 187.956749.
The final theorem still recovers the exact original Chen existence statement.
The independent production qualitative and 0.67 counting cutoffs are unchanged.