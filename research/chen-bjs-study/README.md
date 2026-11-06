# Numerical Chen with proved BJS sieve inputs

This package proves Chen existence at an explicit numerical cutoff, using the
sharp BJS sieve implementation and the existing power-saving Euler-product
bound. It introduces no local axioms. Its only nonstandard axiom is the
permitted production hypothesis `ChenEffective.dirichlet_seven_eighths`.
No OpenAI modules or new external dependencies are imported.

## Current result

`BJSStudyChen.lean` proves that every even N >= bjsStudyN0 is a prime plus
a prime or a product of two primes, where

    bjsStudyN0 = 3^(3^2700).

The natural double-exponential coordinate is H = log(log(N0)),
approximately 2966.347227. `BJSStudyCompatibility.lean` recovers the exact
original public Chen statement without using the old implicit Chen proof.

The older qualitative production theorem at 3^(3^2900), and the stronger
0.67 counting theorem, are unchanged.

## Proved product input and cutoff

`BJSProvedProductProfile` selects U=3^2652 and relative error 1/10000.
Its feasibility is the finite rational inequality

    130000000000000 * U^(-1/68) <= 1/20000.

Because 2652=68*39, this reduces to arithmetic involving 3^39. The actual
Euler-product theorem is already proved in `OptimizedEulerProductPower`;
no finite prime table or sharp prefix assumption is needed.
`BJSStudyProducts` transports this profile to the relative error 1/4000
required by the sharp density theorems.

The larger pre-sieve product Q costs log(Q)<=2U. The geometry proof pays

    log(N) >= 10^20 * (1+2U).

The exponent 43 pays the fixed scalar, and 2652+43=2695<=2700.
The selected cutoff also dominates the fixed mass, distribution, divisor,
prime-pair and triple-remainder thresholds.

| Component | Selected allocation |
|---|---:|
| Product endpoint U | 3^2652 |
| Proved product relative error | 1/10000 |
| Relative error supplied to density adapters | 1/4000 |
| Density theorem epsilon | 1/2000 |
| Both density coefficients | 110 |
| Base coefficient loss | 1/20 |
| Medium coefficient loss | 113/100 |
| Endpoint loss | 1/20000 |
| Weighted coefficient | 2.02575 |
| Triple main coefficient | 3.94033 |
| Triple remainder allocation | 1/100 |
| Positive final margin | 0.050585 |

## Audit

There is no `bjsStudy_interval` axiom in the active package.
The source audit rejects every local axiom, proof placeholder, native_decide,
unsafe declaration, compiler-trust bypass and OpenAI import.
`AuditBJSStudy` checks the exact four-axiom ledger (Lean's three standard
axioms plus Dirichlet) for the final theorem and its compatibility theorem,
and traverses the proof to reject use of the old implicit Chen proof or
the separate production/counting proofs. It also rejects an environment
that still contains the removed BJS interval axiom.

Both density adapters and their entire continuous/discrete proof chain
use only standard axioms. The active product estimate uses Dirichlet.

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

## What dominated the archived H=188 study

The study-specific finite cap^20 = 3^(20*10^80) costs
H approximately 187.2966. The archived tower 3^(3^171) covered it.
Its conditional small-endpoint product geometry cost approximately H=178.58.
The retained prime-pair/denominator threshold costs about H=184.30;
the retained triple remainder payment about H=97.40.
The elementary Mertens divisor gate is now only about H=33.05.
These are sufficient proof thresholds, not mathematical lower bounds.
The active larger-cutoff result is instead dominated by product geometry.

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
* A proved small-endpoint product estimate; the active package has no
  reciprocal-interval axiom to reuse at this endpoint.

`BudgetStudy.ps1` regenerates budget-results.json. Its decimal summaries
are exploratory output; exact coefficients, cutoff equalities and scalar
feasibility assertions are checked separately in Lean.

## Preserved low-cutoff studies

The complete earlier conditional study is preserved by the annotated tag

    study/bjs-low-cutoff-conditional-927c1eb8

at commit 927c1eb8. Its cutoff was 3^(3^171), H approximately 187.956749,
and it depended on one extra reciprocal-prime interval assumption.
See `LOW_CUTOFF_STUDY.md` for its exact status and retrieval instructions.
That assumption is absent from the active source and proof.

The useful axiom-free or explicitly conditional study modules remain here:
`BJSStudyH36` and `BJSStudyFiniteTail` provide scalar H=36 feasibility and
finite-tail tools; `BJSMertensThetaTarget` gives the conditional theta-to-prefix
and exact-composite-endpoint interval bridge at 3^120; the reciprocal-prefix
modules prove the finite lower base through 286 and the Dirichlet-only tail
from 3^3072. The unproved theta premise and missing middle range are not
inputs to the active numerical Chen theorem.

Reducing H again requires a stronger proved product profile at smaller U,
followed by propagation of its geometry and error budget. The preserved
studies can be reused for that purpose without reintroducing axioms.

`BudgetStudy.ps1` regenerates `budget-results.json`. Decimal summaries are
exploratory; the exact cutoff and coefficients are separately checked in Lean.

## Rebuild

Run `.\check.ps1` from this installed research directory after building the
production dependencies. For a final dependency audit with existing artifacts,
run `.\check.ps1 -FromModule AuditBJSStudy`.
