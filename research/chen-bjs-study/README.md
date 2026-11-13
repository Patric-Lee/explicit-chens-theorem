# Numerical Chen with proved BJS sieve and explicit-formula inputs

The Dirichlet input is now supplied by the proved, vendored OpenAI theorem.
Its transitive audit passed with standard Lean axioms only. The complete active Chen
closure and combined integration audit passed on Lean 4.34.1 and the exact upstream Mathlib pin.
The active Chen audit allowlist is standard-only. No new external Lake
packages, BJS axioms, placeholders, or native_decide proofs were added.

## Current result

`BJSTightChen.lean` proves the complete Chen existence statement for every
even N>=3^(3^134), corresponding to H approximately 147.308095. It uses
K=8.2, square epsilon=1/100, and the new prime-pair allowance 10^-4.
`ChenEffective.TightBudget.original_chen` recovers the original literal
statement. Earlier final Chen proofs are excluded from its dependency closure.

Source masses, actual base/varying distribution inputs, prime-pair main terms,
square analytic inputs, and scalar pre-sieve geometry also have independently
proved producers near H=30. These have not yet been assembled into a complete
H=30 Chen theorem. The complete triple remainder is now proved at H approximately 29.335;
the small-endpoint relative product and lower-count assembly remain open.
See [H30_TRIPLE.md](H30_TRIPLE.md) for the exact verified bounds.

See [TIGHT_BUDGET.md](TIGHT_BUDGET.md), `tight-results.json`, and
`AuditBJSTightBudget.lean` for exact contracts, remaining work, and checks.

## Retained earlier results

`BJSStudyChen.lean` proves that every even N >= bjsStudyN0 is a prime plus
another prime or a product of two primes, with the exact cutoff

    bjsStudyN0 = 3^(3^171).

In natural double-exponential coordinates N0=exp(exp(H)), this is
H=171*log(3)+log(log(3)), approximately 187.956749.
`BJSStudyCompatibility.lean` recovers the exact original public Chen statement,
without using the original implicit Chen proof or the stronger counting theorem.
The verified positive end-to-end budget margin remains 0.050585.

## Joint budget and relaxed denominator

The joint-budget branch proves the actual denominator lower bound
`G_N(R) >= log(N)/(8.1*S(N))` from `N >= 3^(3^83)` (H approximately
91.278868), using only standard Lean axioms. It propagates the coefficient
through the actual square and triple counts and recovers Chen existence at
the existing cutoff with positive margin. The complete Chen cutoff remains
`3^(3^171)`: distribution and remainder requirements are still large.

See [JOINT_BUDGET.md](JOINT_BUDGET.md) for the exact proved statements,
local specialization of the squarefree multiplicative sum, and the
now-proved explicit square-root remainder. Numerical studies at H=33,30,29
keep every hypothetical estimate and unpaid producer gate explicit.

## Why the cutoff decreased

`research/chen-dusart` proves the theta and signed reciprocal-prime prefix
bounds from 3^120 by an explicit formula and a numerical zero moment under
the permitted Dirichlet hypothesis. All analytic inputs are proved. No
finite-height RH hypothesis or numerical zero table is assumed.

`BJSStudyProducts.lean` uses that theorem to prove the relative Goldbach
sieve product bound with error 1/4000 at pre-sieve start U=3^120. It includes
the summable prime-square correction and the exact closed-left endpoint.
The geometry pays log(N)>=10^20*(1+2U). The existing finite analytic and
square/triple caps all fit below the common cutoff 3^(3^171).

`BJSProvedProductProfile.lean` retains the independent coarse power-saving
profile at 3^2652, under names beginning `bjsPower`. It no longer supplies
the active smaller-cutoff proof. The previous active cutoff was 3^(3^2700).

The older qualitative production theorem and the stronger 0.67 counting
cutoff are unchanged. No claim is made here of H=120, H=36, or H=29.

## Explicit Selberg two-term expansion

The actual denominator now has a proved expansion with secondary term
`gamma + sum_{p|N} log(p)/(p-1)` and remainder bounded by
`20*exp(1096+log(N)/16)/sqrt(R)` for every positive even N and integer R>=1.
See [the statement and proof map](SELBERG_TWO_TERM.md). The new result uses
only standard Lean axioms; it does not yet change the final Chen cutoff.

## Expanded denominator and optimized final budget

`BJSExpandedDenominator.lean` now uses the proved two-term expansion to obtain
the actual denominator bound from `N >= 3^1000000` (H approximately 13.90956).
`BJSExpandedChen.lean` propagates it through the actual square/triple bounds
to Chen existence, with `K=8.2257261896036` and normalized triple remainder
allocation `10^-40`. It also recovers the original literal Chen statement.
The earlier proof and its larger positive margin remain available.

The new proof supports every `K >= 8.1` satisfying
`K*0.4925401 + 10^-40 < 4.0515`; the displayed choice is within `5*10^-14`
of the strict upper boundary. The analytic error constant remains `10^40`:
only its allocation at the final cutoff has been tightened.

The final cutoff is still `3^(3^171)`, set independently by the lower-count
geometry. See [EXPANDED_CHEN.md](EXPANDED_CHEN.md) for statements, numerical
budget, and audit instructions. The new final proof uses the new expansion
and excludes both earlier final Chen proofs from its dependency closure.

## Certificate reuse study

See [the pinned ternary-Goldbach repository comparison](TERNARY_CERTIFICATE_REUSE.md)
for kernel bit-sieve, rounded arithmetic and Hardy-Z certificate candidates.
The study imports no foreign proof or numerical assumption.

## Checking

Run `research/chen-bjs-study/check.ps1` after the established production
prerequisites are built. Its order first prepares the reciprocal-prime
foundations, then checks the local Dusart package, then the product,
counting, triple and Chen proofs. Existing artifacts can be audited with
`check.ps1 -FromModule AuditBJSStudy`.

`AuditBJSStudy.lean` checks the numerical cutoff, the exact old Chen statement,
standard-only axiom ledgers, the actual proved OpenAI Dirichlet dependency, and the complete final proof closure
for unsafe declarations or unlisted axioms. `source-audit.ps1` independently
scans the local Lean sources. `research/chen-dusart/AuditDusart.lean` audits
the analytic replacement separately.

See `DUSART_STATUS.md` for the exact analytic result and source provenance.
The historical conditional low-cutoff snapshot remains documented in
`LOW_CUTOFF_STUDY.md`; the current proof no longer uses its interval axiom.

## Hybrid product pilot

The [hybrid pilot](HYBRID_PRODUCT_PILOT.md) finds a numerical candidate
using 500,000 selected positive critical-line zeros and finite prime sums
through 2e10. A new kernel-checked positive-moment subtraction theorem
removes the need for a complete zero count or finite RH verification.
The finite-head-to-Mertens analytic bridge is now proved and audited;
the zero boxes, finite sieve/log certificates, constant enclosures and
uniform numerical payment remain unproved. This is numerical feasibility, not a
completed small-endpoint product or an improved final Chen cutoff.
See [the proved analytic bridge and measured kernel benchmarks](HYBRID_BRIDGE_STATUS.md).


## Checked prime-sum certificates

The [minimal PrimeCert-derived sieve and reciprocal-sum adapters](PRIMECERT_SIEVE_PORT.md)
now have kernel-checked concrete prefixes through 100,000, with standard axioms only.
The 100,000 weighted check takes about 51 seconds and 1.96 GB peak working set
under serial elaboration. The full 2e10 grid and H < 30 remain open.

See [the proved 2√x correction and smaller certificate candidate](SHARP_PRIME_POWERS.md).
