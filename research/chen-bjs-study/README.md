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

This theorem depends on the Dirichlet axiom AND the single temporary interval
assumption below. It is not an unconditional improvement of the verified
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

## Axiom ledger

Only `bjsStudy_interval` remains an axiom in this package. Its statement
requires 1<a<=b and b>=286, with error 1/log(a)^2. The original provisional
statement omitted a<=b and was false for reversed endpoints. This was
corrected before the density assumptions were removed; `BJSIntervalOrder`
proves an axiom-free regression counterexample. Production never used it.

`bjsStudy_lower_density` and `bjsStudy_upper_density` are now THEOREMS.
Their exact project-weight statements retain coefficient 110 at epsilon
1/2000, given relative product error 1/4000. Each proof uses only Lean's
three standard axioms. The full provisional Chen theorem uses exactly
those three, Dirichlet, and the single ordered interval assumption.

## Certified sharp sieve implementation

The density adapters are proved by the following chain:

* `BJSLayerTableData` supplies integer candidates for mesh 1/32 at precision
  10^12. `BJSLayerTableChecks` checks their base row, every successor row,
  and every cell's hat envelope, using kernel-reduced `decide`.
* `BJSGridCertificate` proves that the integer recurrence bounds the actual
  normalized continuous layers. `BJSGridProfile` transfers grid certificates
  to EVERY real coordinate in the closed parity domain.
* `BJSLayerProfile` certifies layers 1 through 12, ending with coefficient
  7417/1000000. `BJSAnalyticTail` continues this with factor 241/250 per
  layer, uniformly in the coordinate and depth.
* `BJSSharpHat` gives boundary factor 11/3 and the odd-parity tail factor
  116/125. `BJSSharpRecurrence` caps the corresponding error multipliers
  by 1931/2000 and 1859/2000 at relative error <=1/4000.
* `BJSParitySums` proves both error parity sums are <=220 by an exact
  rational finite prefix and an analytic two-state tail potential.
* `BJSDiscreteEnvelope`, `BJSDiscreteAnalytic` and `BJSDiscreteInduction`
  prove the actual discrete source-layer bound, including inherited versus
  recursive coordinates, natural-ceiling transport, the compact odd case,
  even endpoint, and zero-support case.
* `BJSDiscreteParity` sums the actual layers. `BJSSharpDensity` proves the
  lower and upper Rosser-density statements. The factor-two slack gives
  220*(1/4000)=110*(1/2000), exactly the former axiom statements.

No tabulated BJS constant is assumed. This proves the adapters needed here;
it does not claim every epsilon-dependent entry of the paper's Table 1.
All the named results above use standard axioms only. No new external
modules or dependencies are imported, and no native_decide is used.
The candidate generator's floating-point selections are NOT trusted: every
integer row and final coefficient inequality must pass the Lean checker.

The earlier independent layer-two certificate (coefficient 0.35), elementary
Mertens replacement, reduced finite caps and H=36 scalar feasibility
certificates are retained. The exact counting weights, QD assembly and
actual mass/distribution/triple estimates are unchanged.

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

With the same proved density coefficients, the lower density payment
is <=1/250 and upper <=7/125. A base allocation 3/50 instead of 1/20
leaves final margin 0.040585. The original fixed-power loss is included.

This is scalar feasibility, NOT a Chen theorem at H=36. It requires:

* An all-recursive-interval profile at U=10^9, error <=1/4000. BJS Lemma 18
  alone is insufficient because it requires z>exp(4000). Its small and
  intermediate ranges need proved bridges.
* Actual mass and distribution estimates at H=36, replacing the shared cap.
* Sharper triple absolute moments and remainder estimates at H=36.
* A proof replacing the remaining ordered reciprocal-interval assumption.

`BudgetStudy.ps1` regenerates budget-results.json. Its decimal summaries
are exploratory output; exact coefficients, cutoff equalities and scalar
feasibility assertions are checked separately in Lean.

## Next proof work

Both density adapters are proved and audited; no density axiom remains.

`BJSReciprocalIntervalBridge` proves the closed-left finite-interval transfer
from actual reciprocal-prime prefixes. It approaches the lower endpoint
from the left, so a prime equal to a is retained. In particular, it proves
that the two signed half-log-squared Rosser-Schoenfeld prefix estimates
imply the exact provisional interval statement, with the constant cancelling.
It does NOT assert or assume those prefix estimates as new axioms.

`BJSReciprocalLargeEndpoint` proves both the half-log-squared prefix error
and the requested interval estimate for a>=3^8192, using the existing
Dirichlet axiom only. Its proof retains the existing power-saving Mertens
error, absorbs log(a)^2 with an explicit real-power bound, and pays the
remaining scalar constant numerically. No implicit threshold is used.

The last BJS axiom has NOT been removed. The remaining explicit obligations
are the lower signed prefix estimate for 1<x<3^8192 and the upper signed
prefix estimate for 286<=x<3^8192, relative to the canonical Mertens constant.
`bjsStudy_interval_of_middle_prefix` proves that those two estimates would
close the full statement. Neither premise has been discharged. This is a
substantial analytic range, not a proposed brute-force computation. It
includes the current pre-sieving endpoint 3^120, so the large-endpoint
theorem does not replace the study's product input or improve its cutoff.

The published source is Rosser-Schoenfeld (1962), Theorem 5, (3.17)-(3.18),
https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf. Its range proofs and
numerical inputs are not supplied by merely citing the result. No external
Lean modules, RH assumptions, or new dependencies were imported here.

For the reciprocal interval input, derive the explicit prime estimates
behind Lemma 21 or build a weaker sufficient certified profile. For U=10^9,
use asymmetric endpoint estimates with explicit range bridges. Finite tables
must be checked by Lean certificates without native_decide.

## Rebuild

Run `.\check.ps1` from this installed research directory. Build the production
modules first if their artifacts are absent. For the final dependency audit only,
use `.\check.ps1 -FromModule AuditBJSStudy`. The audit intentionally accepts
the single named temporary interval assumption and rejects any additional one.
