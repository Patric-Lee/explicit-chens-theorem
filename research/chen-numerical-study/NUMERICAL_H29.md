# Platt-only Chen theorem with H < 29

The kernel-checked theorem is
`ChenEffective.H29Conditional.chen` in
[BJSH29ConditionalChen.lean](BJSH29ConditionalChen.lean).
For every even N ≥ N₀ it proves that N is a prime plus a prime or a product
of two primes, with the exact natural-number cutoff

$$
N_0=3^{3\cdot10^{12}},\qquad
H=\log(3\cdot10^{12}\log3)\approx28.82368123221.
$$

`cutoff_lt_double_exp_29` proves N₀ < exp(exp(29)) directly in Lean.
`original_chen` has exactly the original `Goldbach.ChenTheorem` type.
The sole external axiom is the unchanged Platt modulus-one finite RH
statement through height 10⁸. The Dirichlet seven-eighths input is proved.

## Joint variable budget

Put M(N)=S(N)N/(log N)² and L=log N. The budget is

$$
\mathcal M(L)=2.6408-a-\frac b2-e
-\frac12\left[K(0.49254+\eta)+\frac{2C_5}{L^3}+\frac{38}{L}\right].
$$

The final theorem uses a=1/20, b=113/100, e=1/20000, K=8.2 and η=1/10000.
The actual lower count is W(N) ≥ 2.02575 M(N). The actual corrected triple
count has the main term K(0.49254+η)M(N), with raw remainder
C₅N/L⁵ + 19N/L³ and C₅ ≤ 10³⁴. Using S(N) ≥ 1/2 gives the displayed
variable error envelope. At L ≥ 3·10¹² it is at most 0.001, so the margin
is at least 0.005426 > 0. The actual finite counting bridge yields a
representation; no paper coefficient is substituted for a counting theorem.

## Lower-count parameters

The product profile and its pre-sieve start U=4,000,000 are unchanged.
The contraction satisfies

$$
\Delta s=\frac{10\log(2Q)}L
\le\frac{10(1+2U)}L\le\frac1{30000}.
$$

Both exponent losses are 1/300,000,000. The BV exponents are 230 for the
base and 290 for the weighted sum. The proof establishes
10¹¹ log L ≤ L for L ≥ 3·10¹²; each mB is below 10¹¹. Thus the requested
levels fit the proved BV ranges. The base mass budget remains 20,000,000
and the medium mass budget 5,000,000. The lower sieve-factor allowance is
9/2500, which still fits the 1/20 base loss; the medium allowance remains
7/125 and still fits the aggregate 113/100 loss.

## Sharper Mertens normalization

The Pan normalization now uses the proved H30 sharp Mertens product. Its
r=2 input is available at max(3¹⁴⁴,3¹³), replacing the older normalization
input with exponent 3,600,000,000,008. All quotient, prime-pair, support,
distribution and remainder thresholds are checked to fit the new cutoff.
The Selberg-square and Q/complement counting estimates are unchanged in
meaning and are connected to the actual corrected triple penalty.

## Assumptions, audits and reuse

[AuditBJSH29Conditional.lean](AuditBJSH29Conditional.lean) checks the exact
public statement has no extra prefix-window premise. It requires the
actual lower/triple producers, sharper Mertens normalization, variable
budget, completed finite prefix proof and actual OpenAI Dirichlet proof.
It rejects the old H30 Chen theorem and old normalization as shortcuts,
unlisted axioms, unsafe proof dependencies, placeholders and native compiler
trust. The combined integration audit checks the H29, H30 and standard-only
recoveries of the original Chen statement.

[FINAL_CHEN_H29_AUDIT.json](../chen-platt/FINAL_CHEN_H29_AUDIT.json) records the
active source/object hashes and dependency provenance. Only the existing
mathlib and LeanArchitect external packages are used. The finite count/log
certificates are reused unchanged; no new manual certificate campaign is
required. The [15+ hour first-build and memory guidance](../chen-platt/README.md#build-time-and-memory)
still applies to a source-only checkout.

For the canonical audit report, from a configured checkout in PowerShell:

```powershell
$env:CHEN_BUILD_TAG = 'jointbelow'
$env:CHEN_BUILD_JOBS = '1'
$env:CHEN_LEAN_THREADS = '1'
$env:CHEN_LEAN_MEMORY_MB = '12288'
node --expose-gc OpenAI/tools/build-source.mjs AuditBJSH29Conditional AuditBJSTightBudget OAI.AuditChenIntegration
node --expose-gc research/chen-platt/tools/AuditCompletedH29Chen.mjs .
```

The Lean memory setting is an allocator limit, not a cap on total operating
system committed memory; the resource guide records the larger observed
import/audit process usage.
