# Complete Chen theorem below H = 12.5

The exact cutoff is

$$
N_0=3^{240000}<\exp(\exp(12.5)),\qquad
\log\log N_0\approx12.48244202994.
$$

For every even natural number $N\ge N_0$, the theorem
`ChenEffective.GRH125.chen_explicit` in
[AuditGRH125Chen.lean](AuditGRH125Chen.lean) gives a representation as a prime
plus a prime or a product of two primes. Its `original_chen` corollary has
literally the original `Goldbach.ChenTheorem` type.

Full Dirichlet GRH remains the sole additional axiom. The numerical, sieve,
distribution, lower-count, and triple-count bounds are proved. No new
external dependency or `native_decide` is used. The earlier H < 13 theorem
and its audit remain available.

## Complete counting budget

Write $L=\log N$ and $M(N)=\mathfrak S(N)N/L^2$. The actual counts satisfy

$$
W(N)\ge2.02575M(N),\qquad T(N)\le4.0015M(N).
$$

The corrected finite counting bridge therefore gives

$$
R(N)\ge W(N)-\tfrac12T(N)\ge\frac1{40}M(N)>0.
$$

The proof uses the uniform lower bound $L\ge263000$, proved from the exact
natural-number cutoff, rather than assuming a decimal approximation to it.

## Refined pre-sieve moments

[GRH125Moments.lean](GRH125Moments.lean) processes 52 intervals with square
integer endpoints. Each step retains the difference of cumulative theta
sums. The elementary theta bound gives a short compensated recurrence;
each rational step is checked in Lean. This avoids both prime enumeration
and a large branching partition proof.

The resulting root moment is

$$
\sum_{p\le4000000}\frac1{\sqrt p}\le500,
$$

replacing 710. For the Goldbach density, large primes satisfy

$$
\frac{\sqrt p}{p-1}\le\frac{101}{100\sqrt p}\qquad(p>100).
$$

The small-prime contribution is bounded separately, giving

$$
\frac{101}{100}\cdot500+\frac14\cdot20+1=511<512.
$$

Thus the relevant reciprocal and density divisor moments are at most
$e^{500}$ and $e^{512}$, replacing $e^{710}$ and $e^{889}$. At
$C=\lfloor N^{1/200}\rfloor$, the complete pre-sieve envelope satisfies

$$
336L^6\exp\left(512+\tfrac12\log2-L/400\right)\le10^{-12}
\qquad(L\ge263000).
$$

The pre-sieve starting endpoint remains 4,000,000. The already completed
reciprocal-prefix certificates and analytic tail are reused.

## Stronger moving input and specialized distribution budgets

The proof propagates the checked [strong moving input](STRONG_MOVING.md)
through the actual primitive and principal low-conductor aggregates. These
retain exponent $501/1000$ and are already paid for $L\ge10000$. The old
$127/128$ moving bound is not used on the new complete proof path.

High-conductor estimates retain distribution level $N^{0.498}$. Their
logarithmic payments use the application degrees and explicit coefficients:
the generic degree-12 payment uses $10^{30}\le e^{70}$ instead of the much
larger $e^{120}$ bound. The logarithmic cutoff gates are restricted to the
degrees actually needed. No AP-distribution estimate is added as an axiom.

The source mass bounds retain $r=20000000$ for the lower estimate and
$r=5000$ for the upper estimate. Their explicit thresholds remain below
the new cutoff.

## Joint square and triple budget

The prime-pair grid retains its symbolic 200,000-cell mesh. The interval
error is $1/L^2$; retaining its smaller value reduces the finite-grid
allowance from 0.001501 to 0.0001 and the proxy coefficient from 0.49784
to 0.49644. The genuine logarithmic-integral remainder is bounded by
$N/(5000L)$, so the main coefficient 0.498 still suffices.

The Selberg radius stays $\varepsilon=1/500$. Its denominator coefficient
is $K=8.0326$, with the floor reserve $1/150000$. The complete square-error
allowance is rebalanced to $M(N)/1000$, rather than imposing the earlier
$M(N)/32000$ allowance. The actual distribution constant still obeys
$C_5\le10^{12}$; no sharper constant is assumed.

The complementary triple residual is at most $M(N)/6000$. Consequently,

$$
T(N)\le\left(8.0326\cdot0.498+\frac1{1000}+\frac1{6000}\right)M(N)
<4.0015M(N).
$$

## Verification and reproduction

The analytic assembly is [GRH125Analytic.lean](GRH125Analytic.lean). The
final [Chen audit](AuditGRH125Chen.lean) checks the transitive axiom closure,
rejects unsafe and native compiler-trust proof paths, checks literal
recovery of the original Chen statement, and excludes the superseded weak
moving lemmas. The source/object record is
[FINAL_GRH125_CHEN_AUDIT.json](FINAL_GRH125_CHEN_AUDIT.json).

These are repository-local kernel, dependency, and provenance checks. No
independent external comparator, sandboxed independent rebuild, or
alternative-kernel verification is claimed by this release.

From the repository root:

```powershell
$env:CHEN_BUILD_TAG = 'grhtwelvefive'
$env:CHEN_BUILD_JOBS = '1'
$env:CHEN_LEAN_MEMORY_MB = '10000'
node --expose-gc --max-old-space-size=4096 OpenAI/tools/build-source.mjs AuditGRH125Chen
node research/chen-grh/tools/AuditCompletedGRH125Chen.mjs (Get-Location).Path
node OpenAI/tools/audit-sources.mjs --dirichlet-proved
```

There is no new finite certificate campaign. A first source build of the
existing certificates and their assembly has taken **15+ hours** on the
development machine. Full final audits have needed roughly **20–22 GiB of
private committed memory for Lean alone**, distinct from resident RAM.
Existing checked artifacts can be reused after source/object provenance
validation. See the main README for the full build and memory guidance.
