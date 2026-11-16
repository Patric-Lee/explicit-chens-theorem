# Conditional numerical Chen theorem near H = 30

This route now uses the published Platt modulus-one finite-RH result through
height 100,000,000 as its sole external axiom. The temporary reciprocal-prefix
axiom has been removed. The finite window, analytic assembly and final Chen
audits are complete; see [the proof and audit](../chen-platt/README.md).
The existing standard-only theorem remains separate. The former Dirichlet
axiom is supplied by the checked OpenAI proof.

The theorem is `ChenEffective.H30Conditional.chen` in
`BJSH30ConditionalChen.lean`. Its exact cutoff is

\[
N_0=3^{10^{13}}=\exp(\exp(H)),\qquad
H=\log(10^{13}\log 3)\simeq30.02765403654.
\]

For every even natural N at or above this cutoff it proves

\[
N=p+q,\quad p\text{ prime},\quad
q\text{ prime or a product of two primes}.
\]

`original_chen` has the literal type `Goldbach.ChenTheorem`, so the new
route recovers the original project's implicit existence statement.
The cutoff is slightly above H=30; it is not an H<30 result.

## Exact additional assumption

The sole declaration is in `PlattAssumption.lean`:

```lean
axiom platt_modulus_one_finite_RH : TernaryGoldbach.PlattZetaRH
```

It states that every zeta zero with 0 < Re ρ < 1 and |Im ρ| ≤ 10⁸ has real
part 1/2. It is the modulus-one finite statement, rather than full RH or GRH.
The all-real reciprocal-prefix window through 3¹²⁰ and the relative product
bound with tolerance 1/4000 from starting point 4,000,000 are now proved.
The only other axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## Historical numerical pilot studies

These scans and zero-table studies are retained as historical feasibility
work; the final theorem uses the kernel-checked finite window and Platt tail.
They are not theorem inputs.

The saved and rerun scans enumerate 882,206,716 primes through 20,000,000,000.
The fixed-point reciprocal sum is 964832096031544 at scale 2^48; all saved
block sums and counts reproduced exactly. With the wider B1 interval
[0.26149, 0.26151], the rational logarithm grid gives an error enclosure
[-0.000025242597, 0.000066201379], inside [-1/9000, 1/9000].

For the analytic continuation, 500,000 positive zero ordinates from the
previously recorded Odlyzko data give a conservative head moment above
0.0461796 and derivative mass below 19. The moment cap 0.046192 gives a
residual budget W=19e-6. Using the actual definitions of
`BJSHybridAnalyticBridge`, not only the optimized pilot formula, the numerical
envelope at x=2e10 is 0.000105787217, below 1/9000 by more than 5e-6.
The terminal endpoint is b=3^10000. A 10,001-point logarithmic check confirms
decrease through 3^120. These computations support confidence in the input;
they do not certify zero existence or replace the missing uniform Lean bound.

Run `node CheckH30NumericalInput.mjs PATH_TO_ZEROS6_GZ` in this folder to
reproduce the scalar and zero-table checks, and see
`numerical-check.json` for the recorded result. The existing pilot also has
`ValidateHybridPilot.mjs`, which checks the integer/logarithm grid metadata
and error arithmetic. A fresh full scan was rerun in 100.775 seconds on the
development machine; this is JavaScript timing, not Lean certification timing.

## End-to-end inequalities

Let M(N)=S(N)N/log(N)^2. The actual finite counting weights give

\[
W(N)\ge2.02575M(N).
\]

The base source-mass budget is 20,000,000 with exponent loss
1/1,200,000,000. The medium-prime budget is 5,000,000 with exponent loss
1/600,000,000. The proved weighted AP distribution pays the actual QD
remainders; no additional Q factor is inserted.

The medium-prime profile sum is bounded by its integral plus 1/10000,
and the reciprocal mass by 8/5. These bounds are proved in Lean without
the Platt input. They close the aggregate loss at 113/100.

Independently of the Platt input, the complete corrected triple bound
already holds at N>=3^(5*10^12):

\[
T(N)\le[8.2(0.49254+0.0001)+0.001]M(N)=4.040648M(N).
\]

Consequently

\[
W(N)-\tfrac12T(N)\ge0.005426M(N)>0,
\]

and the existing exact finite counting implication produces the representation.
The proof uses the actual base candidates, medium-prime conditioned counts,
Selberg square, Q residual, and complementary triple counts.

## Completed axiom replacement

The complete finite reciprocal-sum/logarithm certificate and the global
coverage proof are checked. The reference R=10¹⁰ cancels the canonical
Mertens constant. The proof needs neither the earlier numerical B₁ enclosure
nor the 500,000 unverified zero ordinates. The old pilot results above remain
available for future studies.

The final audit proves literal recovery of old Chen, requires the actual
lower/triple counts and proved Dirichlet theorem, and rejects placeholders,
unsafe proof dependencies and native compiler trust. Its exact axiom ledger
is the one Platt input and standard Lean axioms. See
[FINAL_CHEN_AUDIT.json](../chen-platt/FINAL_CHEN_AUDIT.json).

From a configured checkout, run
`node OpenAI/tools/build-source.mjs AuditBJSH30Conditional AuditBJSTightBudget OAI.AuditChenIntegration`.
There are no new external Lake packages, and the pinned Lean/Mathlib versions
are unchanged. The numerical theorem remains in its existing namespace so
that previous users can continue to refer to it.
