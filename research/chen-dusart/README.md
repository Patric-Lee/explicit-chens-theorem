# Explicit theta and reciprocal-prime bounds from the proved Dirichlet 7/8 theorem

This package proves, for every real x >= 3^120,

    abs(theta(x)-x) <= (3/4)*x^(15/16)
    abs(theta(x)-x) <= 4*x/log(x)^2
    abs(P(floor(x))-log(log(x))-M) <= 1/(2*log(x)^2).

It also proves the ordered, closed-left reciprocal-prime interval bound
needed by the BJS sieve, including the exact endpoint 3^120.
Public statements are in `DusartPort/Application.lean`.

These are restricted replacements for the Dusart input, derived from the proved Dirichlet theorem,
needed by Chen. This does not claim Dusart's unconditional Theorem 5.2, its
sharper coefficients, or its full small-x range has been formalized.

## Proof and trust boundary

The argument proves xi Hadamard factorization, the positive zero-moment
identity, and a numerical absolute moment at most 3/25. It transfers that
bound to the actual zeta-zero sum with multiplicities. The smoothed explicit
formula, including trivial zeros, then gives an error at most
0.121*x^(15/8) for psi1 at x>=3^100. Explicit unsmoothing gives
abs(psi(x)-x)<=0.7*x^(15/16), and the prime-power correction gives theta.

`AuditDusart.lean` checks exact axiom ledgers and traverses all dependencies
of the numerical results. Its allowlist now contains standard Lean axioms
only: the former Dirichlet axiom is replaced by the compiled and audited
OpenAI proof. The full upgraded Chen and combined integration audits passed. No numerical
zero table, finite-height RH premise, placeholder, native_decide proof, or
new external Lake package is used. Lean and Mathlib have been upgraded to
the exact versions required by that proof.

The supporting analytic proofs are selectively copied and backported as
local source; see `NOTICE.md` and `LICENSE-APACHE`. Upstream packages are not
added to Lake's dependency graph.

## Checking

The current pinned-version validation is
`node OpenAI/tools/build-source.mjs OAI.AuditChenIntegration` from the repository
root. See [the complete audit report](../chen-effective/UPGRADE_434_AUDIT.md).
The older commands below retain their strict warning policy and separate
artifact directories.

The coordinated full build is `research/chen-bjs-study/check.ps1`. It builds
the required reciprocal-prime foundations before this package, then builds
the BJS product, lower/triple counts and Chen theorem.

After those prerequisites exist, this package can also be checked separately:

    research/chen-dusart/check.ps1

To repeat only the final transitive audit on existing artifacts:

    research/chen-dusart/check.ps1 -FromModule AuditDusart

All compilation uses warnings as errors and the Lean kernel. `modules.json`
contains the exact local dependency order; unused upstream studies are excluded.
