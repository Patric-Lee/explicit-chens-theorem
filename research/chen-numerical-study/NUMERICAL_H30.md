# Conditional numerical Chen theorem near H = 30

This is a separate experimental route using a temporary numerical assumption
authorized by the user. It does not replace the existing theorem with only
standard Lean axioms. The former Dirichlet axiom is now supplied by
the compiled, audited OpenAI proof. The upgraded final Chen and combined
integration audits passed; see [the report](../chen-effective/UPGRADE_434_AUDIT.md).

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

The one temporary declaration is

```lean
axiom temporary_reciprocal_prefix_window : HybridProduct.HybridPrefixWindow
```

Writing B1 for the canonical Mertens second constant, this means

\[
\left|\sum_{p\le x}\frac1p-\log\log x-B_1\right|\le\frac1{9000}
\quad(4{,}000{,}000\le x\le3^{120}).
\]

This is an all-real window assertion, not merely a finite table entry. Its
numerical support combines a finite prime scan and an analytic tail evaluated
with numerical zero data. It has **not** been fully kernel certified, and
JavaScript checks are not presented as a proof of the universal statement.
In particular, the numerical zero ordinates are not proved zero boxes.

The existing proved product adapter and Dusart tail turn this assumption into

\[
\prod_{u\le p<z}\left(1-\frac1{p-1}\right)^{-1}
\le\left(1+\frac1{4000}\right)\frac{\log z}{\log u}
\quad(z\ge u\ge4{,}000{,}000).
\]

There are no temporary sieve-density, distribution, lower-count, triple-count,
or final-existence axioms. The transitive audit permits exactly this temporary
prefix input and Lean's standard
`propext`, `Classical.choice`, and `Quot.sound` axioms.

## Numerical checks supporting the input

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
the temporary prefix axiom. They close the aggregate loss at 113/100.

Independently of the new temporary input, the complete corrected triple bound
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

## Removing the temporary input

The current replacement route uses Platt's modulus-one finite RH result
through height 100,000,000 as its planned sole additional axiom. The imported
analytic estimates and their theta conversion have compiled with that result
as an explicit hypothesis. The numerical analytic assembly and complete
finite reciprocal-sum/logarithm certificate are still unfinished.

The new relative comparison to R=10^10 cancels the canonical Mertens constant,
so this route does not need a numerical B1 enclosure or the earlier 500,000
unverified zero ordinates. The old computations above remain historical
feasibility evidence. See [the checked Platt components and remaining work](../chen-platt/README.md).
The temporary prefix axiom has NOT been removed yet, and no Platt axiom has
been installed alongside it. There are no new external Lake dependencies.

To rebuild the Lean proof after building the existing BJS and Dusart packages,
run `./check.ps1` from this directory. `-FromModule AuditBJSH30Conditional`
reruns the final transitive audit against existing build artifacts.

The Dirichlet input is supplied by the vendored OpenAI proof, on its exact
Lean/Mathlib versions. No new external Lake package names are added.
The modules are kept outside `research/chen-bjs-study` so its existing
no-local-axiom source audit and theorem remain intact.
