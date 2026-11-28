# Specialized Chen budget at H = 11, 10, 9, 8

This is a research budget study, **not a new Chen theorem**. The checked
cutoff remains `3^145000`, with H approximately 11.97854. No analytic
estimate proposed below has been introduced as an axiom. Full Dirichlet
GRH remains the sole added axiom of the existing Chen route. No package or
`native_decide` is added.

The [reproducible numerical study](tools/StudyGRHFiniteScaleBudget.mjs)
produces [the complete report](SPECIALIZED_FINITE_SCALE_STUDY.json).
It records the checked baseline manifest and hashes of the source formulas.
Floating calculations and the JS prime sieve propose bounds; they do not
certify them. The separate [Lean arithmetic contracts](GRHFiniteScaleBudget.lean)
have been checked using standard Lean axioms only. They deliberately do not
claim that their analytic hypotheses hold for the actual Chen counts.

## Exact positivity requirements

Write L = log N and M = S(N) N/L^2. Let b be the base loss, m the
medium-prime aggregate loss, e the endpoint loss, K the Selberg denominator
coefficient, P the genuine prime-pair main coefficient, and C5 the full
Selberg distribution-remainder constant. The sufficient counting budget is

$$
W\ge(2.6408-b-m/2-e)M,
\qquad
T\le\left(KP+\frac{2C_5}{L^3}+\frac{38}{L}\right)M.
$$

For the actual corrected representation bridge, R >= W - T/2, positivity
therefore requires exactly

$$
2.6408-b-\frac m2-e-\frac{KP}{2}
-\frac{C_5}{L^3}-\frac{19}{L}>0.
$$

Here is one deliberately uniform sufficient contract:

$$
b\le0.068,\quad m\le1.12,\quad e\le1/20000,
\quad K\le8.06,\quad P\le0.495,\quad C_5\le30000000.
$$

It gives W >= 2.01275 M. The following remaining arithmetic is proved in
Lean, uniformly for every L >= L0:

| Target H | L0 | Sufficient triple cap | Positive margin R/M |
| --- | ---: | ---: | ---: |
| 11 | 59874 | 3.991 | 0.01725 |
| 10 | 22026 | 3.992 | 0.01675 |
| 9 | 8103 | 3.995 | 0.01525 |
| 8 | 2980 | 4.005 | 0.01025 |

The L0 values are downward integer approximations to exp(H). This study
does not package the exponential comparisons or a new integer Chen cutoff
as Lean theorems. The analytic component bounds in this contract, their
connection to the actual counts, and their thresholds remain obligations.
For H9/H8, in particular, the pair bound is stronger than our present
45/L logarithmic-integral error permits. The arithmetic table is not
evidence that those targets are analytically feasible.

## Why the present route cannot simply be retuned

The production Pan level interface requires 39 log L <= delta L. Even
with no pre-sieve truncation, it therefore forces geometric shift at least
390 log L/L:

| H | Minimum shift from Pan alone | Current supported shift window |
| --- | ---: | ---: |
| 11 | 0.07166 | at most 0.1 |
| 10 | 0.17707 | at most 0.1 |
| 9 | 0.43318 | at most 0.1 |
| 8 | 1.04694 | at most 0.1 |

Thus the Pan interface alone excludes H10, H9 and H8 in the present
geometric window. H11 has some room, but the truncation cost also has to
fit. Removing this interface means proving a distribution theorem for
the actual sources and weighted convolution; changing its threshold by
hand, or citing a sharper pointwise prime-AP bound alone, is insufficient.

The current interval error eta = 1/L^2 is another serious loss. The
existing grid estimates are

$$
E_{\rm med}(n)\le196/n+192n\eta,
\qquad
E_{\rm pair}(n)\le759/n+30n\eta+5n^2\eta^2.
$$

Even optimizing n numerically, eta = 1/L^2 gives:

| H | Medium grid error | Pair grid error |
| --- | ---: | ---: |
| 11 | 0.00648 | 0.00504 |
| 10 | 0.01761 | 0.01370 |
| 9 | 0.04788 | 0.03725 |
| 8 | 0.13019 | 0.10129 |

Increasing grid sizes cannot remove these losses: the interval error grows
with n. They must be reduced before refining the meshes.

## Retain the existing theta decay

The existing analytic input is

$$
|\theta(x)-x|\le\tfrac34x^{15/16}\qquad(x\ge3^{120}).
$$

Partial summation with f(t) = 1/(t log t), bounding the two endpoints and
integrating the absolute error to infinity, gives the proposed interval bridge

$$
\left|\sum_{u<p\le v}\frac1p-\log\frac{\log v}{\log u}\right|
\le\tfrac34u^{-1/16}
\left(\frac{18}{\log u}+\frac{16}{(\log u)^2}\right).
$$

For u >= N^(1/10), this is at most

$$
\eta(L)=\left(\frac{135}{L}+\frac{1200}{L^2}\right)e^{-L/160}.
$$

All four target scales satisfy the theta theorem's lower endpoint.
At H10 this proposal is about 1.01e-62, instead of about 2.06e-9.
The real-endpoint derivation must still be formalized and connected to
the actual rpowFloor carriers, partitions and boundary conventions.

The study fixes grid sizes at no more than 10^7. These are parameters in
symbolic partition estimates, not a proposal to generate ten million
independent numerical certificates. A uniform symbolic Lean proof still
has to be supplied for the retuned parameters.

## Variable Rankin moments and the joint frontier

Set C = floor(N^theta), let sigma be in (0,1), and let z be the
pre-sieve endpoint. The finite density moment is bounded using

$$
\mathcal M_\sigma(z)
=\sum_{2<p<z}\log(1+p^\sigma\overline\nu(p)),
\qquad
\overline\nu(p)=\frac{1.01+0.25\mathbf1_{p\le100}}p
+\frac{\mathbf1_{p=3}}{\sqrt p}.
$$

The majorant is obtained from `GRHSub12.goldbach_root_prime_tight` by
division by sqrt(p). It also dominates the reciprocal divisor moment.
The study evaluates this finite expression by a JS sieve; the proposed
logarithmic caps are unproved until kernel-certified.

Consider proposed normalized envelopes

$$
E_t\le C_tL^{p_t}
e^{\mathcal M_\sigma+\sigma\log2-\sigma\theta L},
\qquad
E_d\le C_dL^{p_d}e^{-(\delta-\kappa)L}.
$$

The sigma log 2 term pays the floor in C. With error target tau and
g >= 10(theta+delta)+10 log 2/L, the combined necessary range condition is

$$
\frac{\log C_t+p_t\log L+\mathcal M_\sigma+\log(1/\tau)}\sigma
+\log C_d+p_d\log L+\log(1/\tau)
+\kappa L+2\log2\le\frac{gL}{10}.
$$

This inversion identifies the required improvements, rather than treating
the truncation and distribution choices as independent. Positivity and
all other component estimates must still be checked after it holds.

The study samples 20 rational sigma values, six envelope profiles, and
z = 4,000,000 or 300,000. It records no candidate as a proved cutoff.

## A concrete H10 research package

The recommended modeled package retains z = 4,000,000, hence does not
require a new small-endpoint product theorem. It asks for

$$
\sigma=1/4,\quad \mathcal M_{1/4}(4000000)\le17.99,
\quad C_t=16,\quad p_t=1,
$$

$$
C_d=10,\quad p_d=4,\quad\kappa=0,\quad\tau=10^{-4},
\quad\theta=0.0073,\quad\delta=0.00234,\quad g=0.097.
$$

In particular, the complete truncation target is

$$
16L\exp(17.99+\tfrac14\log2-0.001825L)\le10^{-4},
$$

and the sharp distribution target is

$$
10L^4e^{-0.00234L}\le10^{-4}\qquad(L\ge22026).
$$

The first means replacing the current complete tail prefactor 336 L^6
by a substantially sharper source-specific aggregate. It is a target
estimate, not a consequence already proved by changing the Rankin exponent.
The second must cover the relevant weighted source sums. In addition,
the full convolution/QD remainder must retain C5 <= 30,000,000 at this
scale without the old Pan range condition. This is the main analytic risk.

The modeled component values are approximately

$$
K=8.0421,\quad P\le0.494659,\quad
W/M\ge2.021368,\quad T/M\le3.979829,
$$

leaving margin about **0.03145**. These are floating planning results.
The exact Lean contract above is deliberately looser and can be used once
the actual component estimates have been proved. The model reserves
10 tau each in the base and medium loss; these reserve allocations also
need an explicit propagation proof.

The alternative H10 package uses z = 300,000, sigma = 0.3,
moment log cap 17.47, and the less demanding tail prefactor 16 L^2.
Its modeled margin is about **0.02284**. It additionally requires the
relative Goldbach product estimate at this smaller z with the same sieve
tolerance. That estimate is not implied by the smaller moment and is not
assumed true by this study.

## Source and denominator thresholds are separate obligations

The existing source-product and upper-source thresholds have logarithms
about 120,858 and 145,018. They fail all four targets. The source mass
estimates must be proved with their proposed losses at L >= L0, preferably
retaining the power-decaying Mertens error rather than converting it to
coarse inverse-log estimates. Generic `logPowerCutoff` interfaces must also
be replaced by application-specific range proofs where necessary.

For the denominator, the current normalized error uses
S(N) <= exp(822+3L/64), resulting in the large fixed exponent 1918.
A proposed bound S(N) <= 10L would instead give

$$
\log E_{\rm den}\le
\log20+1096+\log(10L)+\tfrac12\log2
-\left(\frac1{16}-\frac\delta4\right)L.
$$

At the recommended H10 parameters the right side is about **-252.09**.
Thus this sharper singular-series bound would pay the existing exp(1096)
kernel remainder without first shrinking its fixed prefactor. The
singular-series bound itself has not been proved in this study. The fixed
1/100000 floor reserve must be replaced by a reserve proportional to 1/L;
the model pays 1.5/L and includes it when choosing K.

## H9 and H8: what the study does not support

H11 has positive modeled packages, and H10 has the two packages above.
Neither H9 nor H8 has a candidate inside the current g <= 0.1 window in
the sampled families, even in the optimistic profile Ct = Cd = 1,
pt = 0, pd = 2, kappa = 0 and tau = 1e-4.

At H9, sigma = 0.3, z = 300,000, that optimistic range condition permits
log moment at most **6.52**, versus the proposed **17.47**. Across the
sampled sigma values its least required shift is 0.140, already outside
the supported geometry. This is evidence for a changed sieve/product
architecture, not merely more precise rounding of current constants.

At H8 the optimistic envelope/range model cannot fit even a zero log
moment for any sigma <= 1. This obstruction is specific to the stated
envelopes, tau and geometry; it is not an impossibility result for Chen's
theorem. H8 also needs a sharper prime-interval bridge and a better Li
remainder coefficient than the present 45/L.

## Recommended implementation order

1. Formalize the retained theta interval bridge and propagate it to both
   grids. This uses existing analytic input and exposes real budget slack.
2. Prove the medium-prime reciprocal mass bound log(10/3) + eta instead
   of 4 L^2. This directly removes two powers from the current L^6 tail
   envelope. Then generalize Rankin to sigma and certify finite moments.
3. Trace the remaining tail powers through the restricted divisor sums
   and actual source discrepancies. Establish whether 16 L at the existing
   endpoint or 16 L^2 at a smaller endpoint is the more tractable target.
4. Prove the small-scale source-mass estimates and a linear-in-L
   singular-series cap, then retune the Selberg floor reserve.
5. Prove the specialized weighted GRH distribution and complete
   convolution/QD remainder. This is the largest mathematical uncertainty;
   preserve it as a separate replaceable interface throughout.
6. Only after all actual input estimates and all-real range proofs pass,
   assemble and audit a new Chen theorem. Until then H remains 11.97854.

Reproduce the numerical report from the repository root:

```powershell
node research/chen-grh/tools/StudyGRHFiniteScaleBudget.mjs --output research/chen-grh/SPECIALIZED_FINITE_SCALE_STUDY.json
node research/chen-grh/tools/CheckGRHFiniteScaleStudy.mjs
```

The exact arithmetic check uses the pinned toolchain:

```powershell
lake env lean research/chen-grh/GRHFiniteScaleBudget.lean
```

The study's [arithmetic verification record](FINITE_SCALE_ARITHMETIC_CHECK.json)
binds the checked Lean source and compiled object. It is not a final Chen
audit or a certificate of any proposed analytic bound.
