# Interchangeable end-to-end Chen budgets

This package separates actual counting estimates from numerical exploration.
It introduces no new axioms or external dependencies. The production and BJS
study sources are unchanged. Their established cutoffs remain respectively
`3^(3^2900)` (Dirichlet only) and `3^(3^171)` (Dirichlet plus the three existing
temporary BJS assumptions).

## Proved Lean interfaces

`ChenRouteBudget.lean` provides:

* `ChenCountingModel`: a positive normalization, four actual counting
  quantities, and a proved finite bridge to the project's representation
  count. Different sieve decompositions can supply a different model.
* `ChenLowerProducer` and `ChenUpperProducer`: the main coefficient and error
  envelope, a natural-number validity threshold, and a proof of the estimate
  for every even N above that threshold.
* `ChenErrorBreakdown`: separate product, sieve, mass, distribution, rounding,
  boundary, analytic and other envelopes. Existing aggregate estimates are
  honestly placed in `other`; their decomposition is not invented.
* `ChenRoute`: independently replaceable base, medium, boundary and triple
  producers. `withBase`, `withMedium`, `withBoundary`, `withTriple` preserve
  the required target and normalization types.
* `ChenRouteCertificate`: a specific integer cutoff, proof that every
  producer threshold is paid, and positivity for EVERY even N above it.

The counting margin is

```
base.lowerCoefficient(N)
  - medium.upperCoefficient(N)/2
  - boundary.upperCoefficient(N)
  - triple.upperCoefficient(N)/2.
```

`chen_route_count` gives the corresponding representation lower bound.
`chen_route_original` recovers the exact original `Goldbach.ChenTheorem`.
The aggregate cutoff is the maximum of 9 and all four producer cutoffs.
`chen_route_thresholds_iff` certifies that no producer cutoff is lost.

The generic machinery uses only Lean's standard axioms. It does not assert
an analytic estimate: each producer requires an actual proof field. Its
clean axiom list should not be confused with discharging those proof fields.

## Existing estimates connected to the interfaces

`ChenRouteSource.lean` implements the project's exact Jurkat-Richert counts
and normalization `liuSingularSeries(N)*N/log(N)^2`. Its boundary quantity
is the actual difference between source and corrected weighted counts.

`ChenRouteProduction.lean` assembles separate base, medium, boundary and
triple estimates from the verified qualitative branch. It does not invoke
the old final Chen theorem. The triple error is retained as

```
2*numericalTripleErrorCap/log(N).
```

Consequently the proved margin floor is
`0.015585 - numericalTripleErrorCap/log(N)`. The existing cutoff pays the
last term and recovers the former margin floor `0.010585`.
`productionPaidTriple` exposes the old constant `1/100` allocation as an
alternative producer. `production_route_dominates_paid` proves that the
variable envelope is at least as informative wherever that payment is valid.

`ChenRouteBJS.lean` independently assembles the provisional BJS study inputs.
Its margin floor is `0.055585 - numericalTripleErrorCap/log(N)`, recovering
`0.050585` at its existing cutoff. Its axiom ledger is unchanged: the
Dirichlet axiom and `bjsStudy_interval`, `bjsStudy_lower_density`,
`bjsStudy_upper_density`, plus standard axioms.

The provisional interval input now explicitly requires ordered endpoints
a<=b. Its earlier declaration omitted that condition and was false for
reversed endpoints; the dependent product proof already had the order.
The study includes an axiom-free regression counterexample, and its
dependent modules must be rebuilt with the corrected declaration.

`ChenRouteMixing.lean` supplies an actual mixed route: BJS base/medium and
the production triple producer. Its numerical margin equals the BJS
route's margin, but its cutoff retains the production triple threshold.
This is checked in Lean, along with an explicit cutoff certificate.

A switched BJS triple estimate is not automatically a bound on our actual
triple penalty. A new counting model with a proved bridge, or a proved
comparison adapter and normalization conversion, is required. Bare paper
coefficients cannot be inserted into a proved route.

## Numerical comparison runner

`catalog.json` describes selectable product profiles, sieve constants and
triple estimates. `BudgetEngine.psm1` evaluates them using `H=log(log N)`;
it never constructs N. It supports constant, inverse-log, power-saving and
log-log-over-log error envelopes. Positive sums are evaluated in logarithmic
coordinates. Overflow and underflow remain explicit; a tiny positive error
is not silently certified as zero.

The default grid is H=29,25,20,15. Run in PowerShell:

```powershell
.\CompareBudgets.ps1 -HValues @(29,25,20,15) -OutputPath (Join-Path $PWD 'comparison.json')
.\RenderComparison.ps1
.\TestBudgets.ps1
```

Select profiles with `-ScenarioIds @('million_with_verified_sieve')` or
provide an edited catalog with `-CatalogPath`. Adding another envelope or
coefficient to the numerical catalog does not create a Lean producer.

See `comparison.md` for a short table and `comparison.json` for the complete
component breakdown, temporary assumptions and missing estimates.

The runner explicitly distinguishes:

* Product tolerance and validity of the sieve coordinate windows.
* Local counting margin before the triple remainder.
* The CURRENT inverse-log triple remainder, retaining its coefficient
  `10^40`; it is never replaced by the `1/100` payment at smaller targets.
* Producer cutoffs, unproved product bridges and unported certificates.
* Missing Selberg or switched-bilinear producers. Unknown main terms and
  remainders remain unavailable, not zero.
* Incompatible counting models or normalizations.

All evaluated allocations still need certification in Lean. Every numerical
row has `classification=numerical_budget_only` and
`closedLeanCertificateAtThisH=false`, including positive rows above a known
cutoff. The separately listed formal routes identify actual proved
certificates. Floating-point comparisons are never promoted into theorems.

The initial catalog contains illustrative choices, not a global parameter
optimization. Failure of a row rejects that allocation, not the target H
or the whole sieve method. The research slots deliberately leave room for
new Selberg moments, a switched triple method, and different counting models.

## Validation and rebuild

There are six Lean modules, compiled with warnings as errors, plus fourteen
numerical/contract checks. `AuditChenRoutes.lean` checks the exact original
Chen statement, the separate production/provisional axiom ledgers, and
transitive proof dependencies. It forbids using the old final Chen proofs
to supply the new adapters. `source-audit.ps1` rejects new axioms,
placeholders, native_decide, unsafe declarations and compiler bypasses in
this package.

After building the existing `chen-effective` and `chen-bjs-study` modules:

```powershell
.\check.ps1
```

For just the final audit, with matching compiled artifacts already present:

```powershell
.\check.ps1 -FromModule AuditChenRoutes
```

The explicit prime-product research profiles are labelled obligations.
No source from the external LeanLab repository is imported by this package.
