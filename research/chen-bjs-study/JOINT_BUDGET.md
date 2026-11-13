# Joint budget and Selberg denominator specialization

The current Chen cutoff remains `3^(3^171)` (H approximately 187.956749).
This development proves a weaker denominator coefficient at a substantially
smaller component cutoff and propagates it through the actual square, triple,
and Chen counting functions. It adds no axiom or package dependency.

## Proved numerical denominator improvement

`BJSSelbergLogEnvelope.joint_selberg_denominator_81` (in the `ChenEffective`
namespace, file `BJSSelbergLogEnvelope.lean`) proves, for even N,

    N >= 3^(3^83)  =>  G_N(R) >= log(N)/(8.1*S(N)),
    R = floor(N^(1/4 - squareEpsilon/2)), squareEpsilon = 10^-10.

The component cutoff has H = 83*log(3)+log(log(3)), approximately 91.278868.
The old denominator interface required coefficient 8+10^-7 above 3^(10^80),
whose H is approximately 184.300855 (and also paid a divisor gate).

The new proof retains the full existing envelope

    E(N) <= 10^24*(1+log(log N))^6

and proves `10^24*(1+H)^6*exp(-H) <= 3/2000` for every H>=90. It does not
absorb the polynomial into sqrt(log N). The weaker coefficient 8.1 permits
this error. The exact generic sufficient condition, now proved, is

    1/K + E(N)/log(N) + epsilon/4 + log(2)/(2*log(N)) <= 1/8.

All these component theorems use only Lean's standard axioms.

## Actual counting propagation

`BJSJointTriple.lean` proves the square main coefficient
`K*(0.49254+eta)` using the actual optimized Selberg weights. It also proves
the corrected triple transfer with an arbitrary main coefficient, charging
the same additional 19 to the inverse-log error coefficient.

`BJSJointBudget.lean` exposes the precise joint feasibility condition

    K*(0.49254+eta) + extra + remainder < 4.0515.

The existing weighted lower count is 2.02575*S(N)*N/log(N)^2. With eta=10^-7,
extra=10^-5 and remainder=0.01, K=8.1 leaves margin 0.025957595; K=8.2 leaves
margin 0.00133059. These allocations are proved by exact rational arithmetic.

`BJSJointChen.lean` supplies an actual end-to-end theorem at the existing
cutoff using K=8.1. It does not invoke the old final Chen theorem. The old
distribution, square remainder, and prime-pair thresholds remain visible,
so the smaller denominator cutoff does not yet lower the complete N0.

## What the literature specialization does and does not prove

`BJSSelbergSpecialization.lean` proves the exact local identities for
f(p)=1/(p-2): f(p)-1/p=2/(p*(p-2)), and the vanishing numerator
1-(p-2)*f(p)=0 in the published secondary-term formula. It defines
`gamma + sum_{p|N} log(p)/(p-1)` and proves its positivity.

It also verifies the singular-series-normalized absolute Euler factors:

    p does not divide N:  1 + 2/(p-1)^2,
    p divides N:         (p+1)/(p-1).

The latter is greater than one; it must not be discarded. Its ratio to the
universal normalized factor is at most (1+1/p)^2 for p>=3.

The full two-term expansion now has a direct, unconditional formal proof:

    |G_N(R) - (log(R)+c_N)/(2*S(N))|
      <= 20*exp(1096+log(N)/16)/sqrt(R),
    c_N = gamma + sum_{p|N} log(p)/(p-1).

This holds for every positive even N and every integer R>=1. The exact
secondary term, both endpoint ranges, square-kernel factorization, and an
explicit cap for the N-dependent Euler constant are all proved. The cap is
deliberately coarse; it does not claim the paper's sharp numerical constants.
See [SELBERG_TWO_TERM.md](SELBERG_TWO_TERM.md) and
`BJSSelbergSquareRemainder.lean`. The transitive audit allows standard Lean
axioms only. No Dirichlet axiom is needed for this expansion. The expansion is now propagated through the optimized final proof in
BJSExpandedChen.lean; the same final cutoff remains because of the independent
lower-count geometry. See EXPANDED_CHEN.md.
Reference: https://arxiv.org/html/2003.05887

## Joint numerical studies

`research/chen-interchange-budget/StudyJointBudget.ps1` evaluates the product,
geometry, mass, distribution, denominator, and triple allocations together.
It retains all missing estimates explicitly. `joint-results.json` includes
both the current constants and candidate bounds at H=33,30,29. Candidate
moment constants and triple caps are hypothetical inputs, not formal results.
Every row has `provedChenCutoff=false`, including algebraically feasible rows.

Run `TestJointBudget.ps1` for normalization and failure-mode checks, and
`research/chen-bjs-study/check.ps1 -FromModule BJSSelbergSpecialization` for
the Lean modules and the transitive audit `AuditBJSJoint.lean`.
