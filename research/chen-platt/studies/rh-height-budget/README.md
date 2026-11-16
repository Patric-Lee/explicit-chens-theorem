# RH-height / finite-endpoint budget comparison

This is a numerical feasibility study, NOT a Lean proof. It reuses the
existing untrusted prime-count data; no new sieve campaign was run. No axiom,
production theorem, original certificate input, or checker core was changed.
The existing checked analytic assembly is still at R=10^10.

## Main result

Keep RH height T=10^8 for now. Existing checked analytic inputs, with a newly
retargeted piecewise budget, suggest R=6.4e9. A coarse finite-RH Schoenfeld
bridge suggests R=2e9 with a joint error allocation. The larger T=3e12 gives
only about1.6% extra endpoint saving at the
fixed allocation, or2.6% at a jointly optimized
allocation, when compared using the SAME analytic bridge.

## Envelope and finite data

Let E(x)=sum_{p<=x}1/p-log(log x)-B1. The final window requires
|E(x)|<=1/9000 on[4e6,3^120]. For each trial R we recompute the finite
relative bound F(R) for |E(x)-E(R)| on[4e6,R] using all prior grid cells.
The Mertens constant cancels. We use the proved log checker's outward
33-unit tail at scale2^48 and floor+1 reciprocal rounding, matching the
segment checker. Counts and arithmetic are still untrusted study proposals.
Two exact count-block boundaries,2e9 and6.4e9, were added only to the
in-memory study grid; no original dataset was overwritten.

The analytic bound A(R) includes the theta endpoint uniformly for x>=R,
the full error-kernel integral from R to B=3^512, and2e-8 for the existing
proved far-anchor/error endpoint allocations. Past the finite-RH range,
we retain our already-checked piecewise theta and plateau bounds:

$$
|\theta(t)-t|\le t/2000000+1147\sqrt t+42\cdot10^9

\qquad(t\ge10^{17}).
$$

The candidate literature bridge uses

$$
|\theta(t)-t|\le\frac{\sqrt t\log^2t}{8\pi},
\qquad4.92\sqrt{t/\log t}\le T.
$$

The two T values allow this through approximately1.540e16 and2.169e25.
We deliberately use the convenient smaller caps1e16 and1e25. The
normalized-theta endpoint convention is handled conservatively with an
additional(log t)/2 in theta error, including its endpoint/integral cost.
The main resulting envelope behaves as(3 log R+6)/(8 pi sqrt R).

Sources: [Büthe, Theorem2 and its proof](https://arxiv.org/pdf/1410.7015),
[Platt–Trudgian](https://arxiv.org/pdf/2004.09765).

## Endpoint results

The entries are the first numerically passing points of the chosen study
grid and chosen envelopes. They are NOT global optimality claims or
certified cutoffs. Fixed means A<=59e-6 and F<=50e-6. Joint means A+F<=1/9000.

| Route / RH height | Fixed allocation | Joint allocation |
| --- | ---: | ---: |
| checked-profile | 7.455 billion | 6.085 billion |
| schoenfeld-100000000 | 2.409 billion | 1.894 billion |
| buthe-sharp-100000000 | 1.981 billion | 1.524 billion |
| schoenfeld-3000000000000 | 2.370 billion | 1.845 billion |
| buthe-sharp-3000000000000 | 1.949 billion | 1.497 billion |

Checked-profile means all analytic INPUT bounds/lemmas are already proved;
the newly retargeted assembly and finite replay still need Lean checking.
Both Schoenfeld routes need a new formal analytic bridge. Buthe-sharp uses
theta<=sqrt(t)log(t)(log(t)-2)/(8pi) and discards only a negative kernel
term. The published proof also uses numerical theta bounds through1e11;
that route needs new certificates or an alternative derivation. It is not
currently a cheap drop-in consequence of our local Platt hypothesis.

The coarser Schoenfeld route can avoid that theta computation: Büthe's
psi<=sqrt(t)log(t)(log(t)-3)/(8pi) error, combined with our proved
psi-theta<=2sqrt(t), suffices once log(t)>=16pi/3. Every candidate range
here meets that condition. The psi bridge still requires formalizing its
analytic kernel estimates and finite parameter tables; accepting the paper
without that proof would introduce an additional unproved input.

## Recommended targets and allocation

With current inputs at R=6.4e9:
A=63.693e-6, F=45.765e-6,
total=109.459e-6 <111.111...e-6.
There are48799 planned count chunks versus76265
at the original endpoint. This is the lower-formalization-cost candidate.

With the coarser bridge and unchanged RH height1e8 at R=2e9:
A=64.094e-6, F=45.620e-6,
total=109.715e-6. The convenient prospective allocation is

$$
A\le65/10^6,\quad F\le46/10^6,
\qquad111/10^6<1/9000.
$$

This leaves1.396e-6 actual numerical slack in the study.
The finite counting RANGE is80.0%
smaller, with3859741 count blocks and approximately
15229 count chunks of at most131072 integers.
The log grid has188640 points /737 chunks;
the logarithm workload declines much less than the counting range.
These are volume estimates, not measured full-campaign runtime guarantees.

## Validation, limits, and next step

comparison.json records candidates, rounding, source/input hashes and
all budget contributions. validation.json independently checks finite
extrema against a direct per-cell scan, checks integral upper envelopes
against numerical quadrature, and checks both finite-RH range conditions.
This does not replace kernel verification.

Do not change the axiom on the strength of this comparison. First Lean-check
the6.4e9 retarget if minimizing immediate work, or pilot the coarse psi-to-
Schoenfeld bridge if a roughly5-fold smaller counting range justifies the
analytic formalization. Do not claim the2e9 endpoint until that bridge and
the finite certificate/global coverage are checked. H around30 is retained;
no smaller Chen H has been proved by this study. Existing manual results
remain reusable. The current manual runner still describes the original
R=1e10 dataset and is intentionally unchanged.

To reproduce the numerical scan:

~~~powershell
node research/chen-platt/tools/CompareRhHeights.mjs
node research/chen-platt/tools/SummarizeRhHeightBudget.mjs
~~~
