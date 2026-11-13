# Verified analytic bridge and kernel benchmarks

The analytic bridge is now proved, but **H < 30 is not proved**. The complete
Chen theorem remains at `3^(3^134)`, or H approximately 147.308095.
This page separates the actual theorems from the remaining certificate work.

The [PrimeCert-derived checker](PRIMECERT_SIEVE_PORT.md) now certifies actual
reciprocal-prime prefixes through 100,000. The old naive benchmark below is
retained as historical evidence. The full 2e10 prime/log grid is still open.

## Actual analytic bridge

Write

\[
F(x)=\psi_1(x)-x^2/2,\quad
q(x)=\frac{\log x+1}{(x\log x)^2},\quad
r(x)=\frac{2\log^2x+3\log x+2}{x^3\log^3x}=-q'(x),
\]

and let E(x) be the actual reciprocal-prime prefix error relative to the
canonical Mertens second constant. For 2 <= a <= b the proof gives exactly

\[
E(a)=E(b)+\frac{\theta(a)-a}{a\log a}-\frac{\theta(b)-b}{b\log b}
 -\left[F(b)q(b)-F(a)q(a)+\int_a^b F(t)r(t)\,dt
 -\int_a^b(\psi(t)-\theta(t))q(t)\,dt\right].
\]

The derivative of F is proved as a right derivative, including at integers.
Thus integration by parts does not assume differentiability across the kinks.
The zero sum is reindexed by the actual xi zero divisor, with multiplicities.
The finite head need not be complete: every omitted zero remains in the
positive-moment residual W.

For a finite head on the critical line, with derivative mass at most A and
absolute omitted-zero moment at most W, the actual unsmoothing theorem is

\[
|\psi(x)-x|\le h/2+2+A\sqrt{x+h}
 +\frac{W((x+h)^{15/8}+x^{15/8})}{h}+2/h
\quad(h>0,\ x-h>1).
\]

The constant residue cancels before unsmoothing. It is not charged as 10^9/h.
The raw integrated error retains its separate powers:

\[
|F(t)|\le(3/25)t^{3/2}+Wt^{15/8}+2t+10^9.
\]

With c(L)=2/L+3/L^2+2/L^3, the proved uniform finite-interval bound is

\[
\left|\int_a^b F(t)r(t)\,dt\right|
\le c(\log a)\left[\frac6{25}a^{-1/2}+8Wa^{-1/8}
 +2a^{-1}+5\cdot10^8a^{-2}\right].
\]

The actual prime-power correction satisfies

\[
\left|\int_a^b(\psi-\theta)(t)q(t)\,dt\right|
 \le34\left(\frac1{\log a}+\frac1{\log^2a}\right)a^{-1/2}.
\]

`ChenEffective.HybridProduct.actual_prefix_from_head_dusart` assembles these
bounds and supplies E(b) from the existing proved Dusart branch when b >= 3^120.
Its head bounds remain explicit hypotheses to be discharged by certificates;
they are not local axioms. The theorem `actual_prefix_without_zero_table`
also supplies a concrete empty-head instance with A=0 and W=9/100,
using the already proved global moment and no zero-table hypotheses. `AuditBJSHybridBridge` checks 69,681 constants,
requires the actual analytic producers, rejects unsafe declarations and
unlisted axioms, and accepts exactly the existing Dirichlet axiom plus
propext, Classical.choice and Quot.sound.

## Measured small certificate batches

These are wall times on the current Windows machine, including Lean startup
and elaboration. They are measurements, not mathematical bounds.

| Batch | Kernel result | Wall time |
| --- | --- | ---: |
| Reciprocal-prime prefix through 0 | passed; standard axioms only | 40.286 s |
| Reciprocal-prime prefix through 100 | passed; standard axioms only | 37.156 s |
| Reciprocal-prime prefix through 1,000, naive normalization | stopped; no certificate claimed | 210.268 s |
| Prime block [900,1001) | passed; standard axioms only | 41.113 s |
| First-zero endpoint term boxes | passed | 76.444 s |
| First-zero assembly | passed; standard axioms only | 15.656 s |

The stopped prefix run reached 7,430,676,480 bytes peak working set and
130.016 CPU seconds. A bounded block succeeds, but this does not establish a
practical method for certifying all primes through 2e10. A verified segmented
sieve and compact arithmetic/log checker remain necessary before scaling.

The zero benchmark proves an actual critical-line zero with ordinate in
(14.13,14.14). Its audit traverses 57,553 constants with standard axioms only.
It proves neither minimality, simplicity, completeness, a 1e-6 box, nor a
high-height batch. It uses an order-four Euler--Maclaurin evaluator with 30
terms at each endpoint. The remainder grows with height; these measurements
do not justify extrapolation to 500,000 boxes up to ordinate 319,388.

The benchmark sources are the 11-file Mathlib-only proof closure from
[IEANTN, pinned at d60421f](https://github.com/teorth/IEANTN/tree/d60421f10c16f5f6c2cb75f1067a72e24e616391/Solutions/RosserSchoenfeld.v2),
under its Apache-2.0 license. They live only under
`hybrid-pilot/kernel-benchmarks/zero`; production Chen modules do not import
them. `zero-sources.json` records URLs, hashes, and the one unused-binder
rename. A tactic-style linter is disabled for this upstream benchmark;
proof kernel checking remains enabled. No OpenAI module or Lake dependency
was added.

## Remaining obligations for H below 30

1. Certify the actual finite critical-line head, disjoint boxes, derivative
   mass <= 19, positive head moment >= 0.0461796, and total positive moment
   <= 0.046192. Raw zero tables do not discharge these statements.
2. Certify finite reciprocal-prime sums, logarithms, endpoint interpolation
   and the Mertens-constant enclosure (or a proved alternative anchor).
3. Prove the uniform numerical payment for the actual analytic bridge,
   then discharge `HybridPrefixWindow`; its previous floating-point pilot
   remains exploratory.
4. Transport the small-endpoint product into the complete actual lower
   count, including pre-sieving, source mass, weighted distribution and
   medium-prime aggregation. The current distribution threshold alone is
   still `3^(10^13)`, H approximately 30.028, and needs a small reduction.
5. Combine the lower count with the already proved complete fifth-order
   triple estimate at `3^(5*10^12)`, recover the original existence theorem,
   and audit the resulting complete proof and numerical cutoff.

The benchmark gate has therefore not cleared large-scale certification.
There is no unconditional small-endpoint product or complete H < 30 Chen
theorem hidden behind the newly checked bridge.

