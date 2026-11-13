# Reuse assessment for the two H≈30 numerical certificates

Inspected source snapshots (not imported into the Chen project):

- calr3/ternary-goldbach: `ab016043e852c126492310d8fc44ea7849c381b2`, Lean 4.35.0.
- gersh/ternary-goldbach-lean: `27df23af6a712895f22204d0d81102baa74f0ebe`, Lean 4.32.1.

This is source inspection, not a fresh build or transitive kernel audit of either foreign closure. Our Chen project remains on the exact OpenAI Lean 4.34.1 / Mathlib pins. No foreign package dependency or axiom was added.

## Most useful finding: calr3's vendored finite ψ campaign

[`PsiFinite.Final`](https://github.com/calr3/ternary-goldbach/blob/ab016043e852c126492310d8fc44ea7849c381b2/vendor/rsbounds/RSBounds/PsiFinite/Final.lean) exposes

\[
|\psi(x)-x|\le\tfrac45\sqrt x\qquad(1500\le x\le10^{10}).
\]

Its comments describe 38,186 checked segments. The pinned Git tree contains 995 campaign files, approximately 31 MiB of campaign source. That is source size, not a compiled-artifact or RAM estimate. The final theorem assembles a finite sieve campaign; it does not itself take finite RH as a theorem parameter. Its complete transitive closure still needs our own audit before adoption.

The [kernel checker](https://github.com/calr3/ternary-goldbach/blob/ab016043e852c126492310d8fc44ea7849c381b2/vendor/rsbounds/RSBounds/PsiFinite/Kernel.lean) is especially relevant: no Mathlib import in the evaluator, raw recursors, direct natural-number bit operations, word-parallel composite masks, SWAR population counts, forced accumulators, fixed-point enclosures, and separately proved soundness. This is substantially more appropriate for a large kernel computation than per-integer trial division or exact rational summation.

Two possible uses:

1. Reuse the proved finite ψ bound as an analytic input on its finite range, transporting definitions and bounding our weighted integral. If its bound applies throughout `[a,b]`, then
   \[
   \left|\int_a^b(\psi(t)-t)\frac{\log t+1}{t^2\log^2t}\,dt\right|
   \le\tfrac45\int_a^b\frac{\log t+1}{t^{3/2}\log^2t}\,dt.
   \]
   This still requires endpoint anchors, prime-power corrections and the continuation above `10^10`. It is not by itself our reciprocal-prefix theorem.
2. Adapt the minimal sieve to our own fixed-point reciprocal-prefix checker. For a block with `0<a≤p≤b` and certified prime count `c`,
   \[
   c/b\le\sum_{p\text{ in block}}1/p\le c/a.
   \]
   Adaptively sized blocks and directed rounding can replace individual reciprocal updates. Their accumulated width error must be explicitly checked against the `1/9000` prefix allowance.

## Finite RH: distinguish the assumed large range from proved small zeros

Calr3's pinned [`Statement.lean`](https://github.com/calr3/ternary-goldbach/blob/ab016043e852c126492310d8fc44ea7849c381b2/TernaryGoldbach/Statement.lean) explicitly says its two published computational hypotheses are not formalized. `PlattGRH` supplies RH up to `10^8` at modulus one. A standard-only axiom report for a theorem taking this hypothesis is not a proof of that hypothesis.

There is also a genuinely different [height-100 certificate](https://github.com/calr3/ternary-goldbach/blob/ab016043e852c126492310d8fc44ea7849c381b2/vendor/rsbounds/rh100/README.md): the repository reports a checked 99-module closure locating 29 positive zeros through height 100, including completeness and simplicity, tied to Mathlib's zeta. It is adapted from teal-sea/zeta-lab and has its own replay ledger.

That does not provide our proposed 400,000-zero head near height 260,877. However, the Hardy-Z evaluation and rational sign/bracket infrastructure is a promising starting point. Our positive residual-moment argument does not require completeness of the finite head: distinct certified critical-line zeros and their moment/derivative estimates suffice; missed zeros are charged to the proved residual. We should isolate that smaller proof interface. Evaluation cost at the much larger heights must be benchmarked before scaling an Euler–Maclaurin-based checker.

## Gersh: useful kernel machinery, broader external trust boundary

The [standalone kernel-certificate package](https://github.com/gersh/ternary-goldbach-lean/blob/27df23af6a712895f22204d0d81102baa74f0ebe/ext/kernel_certificates/README.md) uses factor witnesses, linked chunks and outward-rounded Mertens accumulators. Its documented rounded campaign reaches 100,043 in 72 shards, with a reported cold replay of 16m40s and peak RSS about 6 GiB. Those are that project's measurements, not a benchmark for our billion-scale task. Its generators are untrusted; Lean checks the witnesses and transport theorems.

The broader project also admits external execution claims and literature atoms. Its [Platt–Trudgian comparison card](https://github.com/gersh/ternary-goldbach-lean/blob/27df23af6a712895f22204d0d81102baa74f0ebe/problems/ternary-goldbach/citations/platt-trudgian-rh-zeta-3e12.md) explicitly treats RH through height 3,000,175,332,800 as an external finite-verification input and says no production provider receipt is attached. Its [derived zero-head card](https://github.com/gersh/ternary-goldbach-lean/blob/27df23af6a712895f22204d0d81102baa74f0ebe/problems/ternary-goldbach/citations/derived/platt-zeta-zero-head-sum-3e12.md) also records a `native_decide` dependency. Those particular results cannot be adopted as standard-only proofs under our rules. The underlying algebra and receipt-free kernel checkers can still be studied or selectively ported.

## Recommended next pilot

Start with the minimal bit-sieve and a reciprocal-block transport theorem, then measure a modest campaign with kernel checking enabled. Separately replay a small Hardy-Z bracket batch and measure scaling at our target heights. Audit exact propositions, multiplicities, dependencies, interval enclosures and shard seams before importing a result. Preserving the existing prefix contract preserves the existing conditional cutoff `3^(10^13)`, H≈30.027654; neither repository currently supplies an independently audited drop-in proof of our entire prefix window.
