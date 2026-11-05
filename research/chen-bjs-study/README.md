# Provisional BJS Chen budget study

This is an explicitly conditional research branch, authorized by the user.
It is not imported by the production theorem in ../chen-effective.
The production theorem remains at commit 6b412908 with its single local
Dirichlet axiom and cutoff 3^(3^2900). The 0.67 theorem is untouched.

## Current result

`BJSStudyChen.lean` proves the exact prime-plus-P2 conclusion for every even
N >= bjsStudyN0, where `bjsStudyN0_eq` fixes bjsStudyN0 = 3^(3^171).
Its natural double-exponential coordinate is H approximately 187.956749.
The proof recovers the original public Chen specification in
`BJSStudyCompatibility.lean`, without using its old implicit proof.

This theorem depends on the Dirichlet axiom AND the three temporary BJS
assumptions below. It is not an unconditional improvement of the verified
production cutoff. No OpenAI modules or new external dependencies are used.

| Component | Selected allocation |
|---|---:|
| Product endpoint U | 3^120 |
| Product relative error | 1/4000 |
| Density theorem epsilon | 1/2000 |
| Both density coefficients (rounded up) | 110 |
| Lower density error | 7/2000 |
| Upper density error | 7/125 |
| Medium reciprocal mass | <= 8/5 |
| Base coefficient loss | 1/20 |
| Medium coefficient loss | 113/100 |
| Endpoint loss | 1/20000 |
| Weighted coefficient | 2.02575 |
| Triple main coefficient | 3.94033 |
| Triple remainder allocation | 1/100 |
| Positive final margin | 0.050585 |

The finite counting identity and QD remainder assembly remain proved project
results. All mass/distribution thresholds are actually paid at the selected
cutoff, rather than left as hypotheses of the provisional final theorem.

## Exact temporary-axiom ledger

All three declarations are in BJSStudyInputs.lean. Reference:
https://arxiv.org/html/2207.09452v6

1. `bjsStudy_interval`: the finite-subset consequence of BJS Lemma 21,
   for a>1 and b>=286, with error 1/log(a)^2. Still unproved in Lean.
2. `bjsStudy_lower_density`: a project-weight adapter of Theorem 6,
   using Table 1 at epsilon=1/2000 and lower coefficient 110.
3. `bjsStudy_upper_density`: the analogous upper adapter, rounding 109
   up to 110. Both adapters still need proofs for the exact source weights.

The product input has error 1/4000, leaving strict slack against the paper's
1/2000 hypothesis. These assumptions contain no final Chen conclusion,
no distribution theorem, and no triple estimate.

The audit expects exactly these three plus the original Dirichlet axiom,
in addition to Lean's three standard axioms. They must not be silently
added to the production whitelist.

## Proved supporting results

The following use only standard axioms, with no temporary BJS assumption:

* BJSStudyElementaryMertens identifies the elementary reciprocal-prime
  constant with the project's canonical constant, using uniqueness of the
  limit. It transfers the already proved elementary 10/log(x) error.
* BJSStudyMertens proves the one-sided product bound actually needed by
  the triple divisor normalization, and inverse product <=6 log(n), from
  n>=3^30. This replaces the old 3^2176 gate. The proof uses exp(E)>=1+E,
  avoiding the unnecessary two-sided exp-error payment.
* BJSStudyFiniteCap re-proves the mass/distribution threshold caps with
  exponent 10^80 instead of 10^100; no new analytic estimate is assumed.
* BJSStudyLogGate proves log(x)^6<=sqrt(x) for x>=10^80 directly using
  log(x)<=16*x^(1/16), replacing the generic logPowerCutoff(6) gate.
* BJSStudyFiniteTail proves a finite-prefix/geometric-tail certificate
  theorem. It does NOT certify the BJS table or the source induction yet.
* BJSStudyH36 proves the scalar geometry and payment certificates below.

BJSStudyProducts proves an all-interval Goldbach product bound from the
single temporary reciprocal-interval assumption. It covers small recursive
upper endpoints, empty intervals, and subsets of odd primes. It does not
assume the stronger, range-restricted BJS Lemma 18. No finite computation
through 10^12 is needed for this coarse bootstrap.

## What dominates H=188

The study-specific finite cap^20 = 3^(20*10^80) costs
H approximately 187.2966. Selecting the simple tower 3^(3^171) covers it.
The current product geometry alone costs approximately H=178.58.
The retained prime-pair/denominator threshold costs about H=184.30;
the retained triple remainder payment about H=97.40.
The elementary Mertens divisor gate is now only about H=33.05.
These are sufficient proof thresholds, not mathematical lower bounds.

## H=36 feasibility result and limitations

At log(N)>=exp(36), U=10^9 and log(2Q)<=1+2U, the exact geometry charge
10*log(2Q)/log(N) is <=10^-5. Its numerical value at the endpoint cap
is approximately 4.63905*10^-6. BJSStudyH36 certifies this using a proved
lower bound for exp(36), not floating-point arithmetic.

With the same provisional density coefficients, the lower density payment
is <=1/250 and upper <=7/125. A base allocation 3/50 instead of 1/20
leaves final margin 0.040585. The original fixed-power loss is included.

This is scalar feasibility, NOT a Chen theorem at H=36. It requires:

* An all-recursive-interval profile at U=10^9, error <=1/4000. BJS Lemma 18
  alone is insufficient because it requires z>exp(4000). Its small and
  intermediate ranges need proved bridges.
* Actual mass and distribution estimates at H=36, replacing the shared cap.
* Sharper triple absolute moments and remainder estimates at H=36.
* Proofs replacing all three BJS assumptions.

`BudgetStudy.ps1` regenerates budget-results.json. Its decimal summaries
are exploratory output; exact coefficients, cutoff equalities and scalar
feasibility assertions are checked separately in Lean.

## Next proof work

For the density adapters, verify finite initial source-layer envelopes,
region-dependent hat transport, and a geometric tail, then connect the
resulting parity sums to the existing exact Rosser weights. The generic
finite-tail certificate is proved; the numerical layer certificates and
improved actual-layer induction remain unfinished. No external numerical
C1/C2 table has been presented as a kernel-checked result.

For the reciprocal interval input, derive the explicit prime estimates
behind Lemma 21 or build a weaker sufficient certified profile. For U=10^9,
use asymmetric endpoint estimates with explicit range bridges. Finite tables
must be checked by Lean certificates without native_decide.

## Rebuild

Run `.\check.ps1` from this installed research directory. Build the production
modules first if their artifacts are absent. For the final dependency audit only,
use `.\check.ps1 -FromModule AuditBJSStudy`. The audit intentionally accepts
the three named temporary assumptions and rejects any additional one.
