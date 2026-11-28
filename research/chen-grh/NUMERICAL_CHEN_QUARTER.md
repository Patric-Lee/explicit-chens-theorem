# Complete Chen theorem from the certified quarter moments

The exact cutoff is

$$
N_0=3^{119081}<\exp\!\left(\exp(11.782)\right).
$$

Its actual logarithmic height is approximately 11.78160704043. The explicit
theorem is `ChenEffective.GRHQuarterChen.chen_explicit` in
[AuditGRHQuarterChen.lean](AuditGRHQuarterChen.lean). It states that
every even natural N >= N0 is p + q, where p is prime and q is prime or a
product of two primes. The theorem `original_chen` has exactly the original
`Goldbach.ChenTheorem` type, checked by definitional equality in the audit.

Full Dirichlet GRH remains the sole added axiom. The route adds no axiom,
dependency, `native_decide`, or numerical oracle. It uses none of the
unproved H = 10 tail or distribution targets.

## Checked counting inequalities

Write L = log N and

$$
M(N)=\mathfrak S_{\mathrm{Liu}}(N)\frac{N}{L^2}.
$$

The actual weighted lower count W and corrected triple penalty T satisfy

$$
W(N)\ge2.00825M(N),\qquad T(N)\le4.015M(N).
$$

The original counting bridge therefore leaves the positive margin

$$
W(N)-\frac{T(N)}2\ge\frac3{4000}M(N)>0.
$$

The lower count is proved in [GRHQuarterChenLower.lean](GRHQuarterChenLower.lean),
the prime-pair main term in [GRHQuarterChenPair.lean](GRHQuarterChenPair.lean),
the actual distribution remainder in [GRHQuarterChenPan.lean](GRHQuarterChenPan.lean),
and the complete square/triple assembly in
[GRHQuarterChenAnalytic.lean](GRHQuarterChenAnalytic.lean).

## Bounds and parameters actually used

The 508 kernel certificates from the [quarter-moment assembly](QUARTER_TAIL_PROGRESS.md)
give both required exponent-1/4 divisor moments with logarithmic cap 17.99,
through the pre-sieve endpoint four million. The new
[sieve bridge](GRHQuarterTruncatedBounds.lean) inserts these moments into the
actual Rosser lower and upper counts. No improved tail prefactor is assumed.

The [core propagation](GRHQuarterChenCore.lean) proves the tail and weighted
distribution payments for L >= 130690, using

$$
C=\left\lfloor N^{13/2500}\right\rfloor,\qquad
D_{\mathrm{distribution}}=N^{1241/2500},\qquad
\varepsilon=\frac9{2500}.
$$

The existing GRH AP estimate with exponent 0.501 is retained. The smaller
distribution level provides a saving of 0.0026. The pre-sieve geometry
shift remains bounded by 0.089. The source upper-mass allowance is 0.021;
the medium-prime loss is 1.139, the base loss 0.063, and the endpoint loss
1/20000. The actual Selberg coefficient is 8.059, the prime-pair main cap
0.498, and the square and triple residual allowances are 1/1000 and 1/3000.

The reduced Pan range pays only the degrees used by the actual argument.
The Selberg radius proof pays its floor loss at the new logarithmic endpoint.

## What the minimum means

This is a certified minimum **within the displayed source-accuracy and
counting package**, not a claim that no other use of the proved bounds or
another Chen sieve can do better. Its source upper-mass estimate requires

$$
\frac{125}{2r}\le\frac{21}{1000},\qquad E\ge40r+1.
$$

Hence r >= 2977 and E >= 119081. Both are proved in
[GRHQuarterChenEndpoint.lean](GRHQuarterChenEndpoint.lean), which also proves
the strict double-exponential comparison. The integer search and its
scope are recorded in `PROVED_QUARTER_CUTOFF_SEARCH.json`.

## H = 10 remains unfinished

The finite exponent-1/4 moment caps are certified. This does not prove the
sharper tail aggregate needed by the H10 budget: the current normalized
prefactor is 26 L^4, whereas the modeled alternatives use 16 L or 0.05 L^2.
The specialized weighted distribution/convolution/QD bounds, smaller-scale
source and denominator payments, actual lower/triple counts on the bands,
and final pasting/audit at H = 10 also remain unfinished.

The positive H10 budgets are conditional arithmetic studies. They show
sufficient targets, not that those targets follow from GRH or from the
existing certificates. Reaching H = 10 with this route is plausible research,
not a promised consequence of the remaining formalization work.

## Verification and reproduction

The [full audit](AuditGRHQuarterChen.lean) checks the original statement's
type, traverses every proof dependency, permits only the standard Lean
axioms and full Dirichlet GRH, and rejects placeholders, unsafe proof
dependencies, native compiler trust and disabled kernel checking. The
source/object record is `FINAL_GRH_QUARTER_CHEN_AUDIT.json`.

The proof is split into serial modules to limit memory peaks. The final
certificate-inclusive theorem and audit still import the earlier large
finite campaign. A fresh full source build of that campaign has taken
15+ hours; historical full checks have used 20–22 GiB of private committed
memory for Lean alone. These certificates are reused when their checked
source and object hashes match.

Use the existing pinned Lean 4.34.1 and Mathlib environment:

```powershell
$env:CHEN_BUILD_TAG = 'grhquarterchen'
$env:CHEN_BUILD_JOBS = '1'
$env:CHEN_LEAN_MEMORY_MB = '8000'
$env:CHEN_BUILD_COMPACT_LEDGER = '1'
node --expose-gc OpenAI/tools/build-source.mjs AuditGRHQuarterChen
node research/chen-grh/tools/AuditCompletedGRHQuarterChen.mjs $PWD
```

The previous [H < 12 proof](NUMERICAL_CHEN_SUB12.md) remains unchanged as a
historical checked result. H = 10 remains a research target.
