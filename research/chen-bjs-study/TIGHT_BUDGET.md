# Tighter Chen budget and inputs near H = 30

The new complete theorem is `ChenEffective.TightBudget.chen` in
`BJSTightChen.lean`. For every even N >= 3^(3^134), it proves the literal
prime-plus-prime-or-two-primes conclusion. `original_chen` recovers the
original `Goldbach.ChenTheorem` specification without using an older final
Chen proof.

The exact cutoff is

\[
N_0=3^{3^{134}},\qquad
H=134\log3+\log\log3\approx147.308094509.
\]

The earlier H = 187.956749 proofs and the stronger counting theorem are
retained. The Dirichlet input is now proved by the vendored OpenAI closure,
whose standard-only audit passed. The upgraded final Chen audit has a
standard-only allowlist and is being rerun. No new external Lake package,
axiom, placeholder, or compiler-based decision proof is introduced.

## What is improved in the final proof

* Geometry now pays log(N) >= 10^6 (1+2U) and permits a coordinate shift
  of 10^-5. The earlier route paid 10^20 (1+2U) for a shift of 10^-7.
  Both the base and conditioned-medium-prime count proofs are rechecked
  with the new tolerance; their existing 1/20 and 113/100 error budgets
  remain valid.
* The finite lower-count cap is reduced from 3^(10^80) to 3^(10^50).
  This is a rechecked cap over actual producer thresholds, not an assumption
  that their numerical constants improved.
* Source masses now use a proved sharp absolute Mertens product estimate,
  obtained from the existing Dusart reciprocal-prefix theorem and the exact
  logarithmic correction constant. Its relative product producer uses
  max(logPowerCutoff 2, 3^(6r+1)), replacing the old coefficient
  1800000000004*r in that threshold.
* The actual prime-pair main term uses a new sharp interval/grid producer.
* The actual square estimate uses epsilon = 1/100 and a sharper moving
  conductor argument. The new Selberg expansion supplies the denominator
  with K >= 8.2 at this epsilon.

For M(N)=S(N)N/log(N)^2, the final proof has

\[
W(N)\ge2.02575 M(N),\qquad
T(N)\le K(0.49254+10^{-4})M(N)+10^{40}N/\log^3N.
\]

It proves the complete theorem for every K satisfying

\[
K\ge8.2,\qquad K(0.49254+10^{-4})+10^{-20}<4.0515.
\]

The displayed choice is K=8.2. At the proved final cutoff, the inverse-log
error is at most 10^-20 M(N), leaving margin
0.005926 - 1/(2*10^20). This allocation is not asserted at H = 30.

## Independently proved inputs near H = 30

| Input | Verified range and conclusion |
| --- | --- |
| Sharp reciprocal-prime interval | log(N)>=10^12; error <=100/log(N)^2 on the Chen exponent intervals |
| Actual prime-pair main term | log(N)>=10^12; coefficient 0.49254+10^-4, with the actual logarithmic-integral weights |
| Square analytic inputs | N>=3^(5*10^12), H approximately 29.334507; epsilon=1/100 |
| Source mass normalization | Same closed cutoff, for every accuracy parameter 0<r<=10^10 |
| Base distribution remainder | N>=3^(10^13), H approximately 30.027654; d<=20,000,000 and the stated modulus budget |
| Varying-q distribution remainder | Same distribution cutoff; d<=10^7 and the stated modulus budget |
| Pre-sieve coordinate geometry | Same distribution cutoff; U<=4,000,000 gives shift <=10^-5 |

The distribution modulus condition is

    m * highBVExponent(A) <= 3*10^11.

The direct proof keeps B*log(log N) in logarithmic coordinates instead of
using the old quadratic logPowerCutoff(m*B). The unweighted base input uses
BV saving 10; the weighted varying-q input uses weighted saving 6, supplied
by BV saving 30. The actual exceptional and nonreduced varying-q corrections
are included. `BJSH30Budget.lean` verifies the concrete choices

    base:   m=1,200,000,000, d=20,000,000;
    medium: m=600,000,000,   d=5,000,000.

It also checks the compatible medium-mass scalar allocation with r=5,000,000
and shifted-prime-integral error 10^-4. With K=8.2, square main allowance
10^-4, and a reserved triple error 0.01, the joint margin is 0.000926.
These are proved inputs and arithmetic allocations, not a full H = 30 Chen
theorem.

## Why the upper analytic cutoff falls

The reciprocal-prime interval error changes from

    1.8*10^13/log(N)

to

    100/log(N)^2.

The two-dimensional prime-pair grid uses 10^7 subdivisions and charges its
mesh error and rectangle errors to a realistic 10^-4 allowance.

For a quotient t=floor(N/a), the old moving-conductor argument spent one
extra logarithmic power and required log(t)>=4^b. The new argument spends
two powers, so it only needs log(t)^2>=4^b. This replaces a cutoff term
3^(4*4^b+1) by 3^(4*2^b+1), with the character-prefix constants and the entire
Pan/square proof chain rechecked. The analytic remainder cap 10^40 itself
has not been improved.

## What still prevents a complete cutoff near 30

1. The final lower sieve still uses the proved relative product profile
   starting at U=3^120. The new geometry certificate says that U<=4,000,000
   would fit near 30, but does not prove that relative product profile there.
   Either prove the profile at that smaller endpoint, or prove a revised
   density budget with a weaker product profile.
2. Assemble the smaller accuracy allocations and the new near-30 mass and
   distribution producers into the complete lower count. The current final
   lower count deliberately retains its older medium-prime summation gate
   and its larger fixed accuracy parameters. The shifted medium-prime
   integral estimate must also be supplied at the newly allocated tolerance.
The former square/triple remainder obstacle is now resolved by the A=5
producer described below and in [H30_TRIPLE.md](H30_TRIPLE.md). The bound
10^40/log(N) remains valid but is no longer the required upper-count route.

## Checking and provenance

All companion modules are adapted from the named existing local source
files, with new namespaces and numerical proofs rechecked. The original
producers are retained. The `BJSTight*` modules supply the complete improved
lower count; `BJSH30*` modules supply the upper branch and the separately
checked near-30 inputs.

`AuditBJSTightBudget.lean` checks the axiom ledgers, traverses the final proof,
excludes the earlier final Chen theorems, and requires the new mass, moving
character, prime-pair, and Selberg-expansion producers in its closure.

Run `check.ps1 -FromModule BJSTightPrimePairThreshold` for a complete rebuild
of this new branch after the retained prerequisites are available. Existing
artifacts can be audited with `check.ps1 -FromModule AuditBJSTightBudget`.


## Update: complete triple remainder at H approximately 29.335

The third obstacle above is now discharged. `BJSH30FifthTriple.lean` proves
the complete corrected triple estimate with a normalized error at most
0.001 for N>=3^(5*10^12). It retains a fifth-order Pan remainder and the
third-order 19 from the Q residual and complementary triples. It does not
need to reduce the older third-order 10^40 constant.

`AuditBJSH30Triple.lean` now permits standard axioms only, using the proved
Dirichlet input. Its upgraded transitive audit is being rerun. The final complete Chen theorem and
its cutoff above remain valid and unchanged. The small-endpoint product
and subsequent lower-count assembly remain unfinished. The product now
has a proved reduction to `SmallEndpointPrefixWindow`; that proposition
is NOT asserted or proved. See [H30_TRIPLE.md](H30_TRIPLE.md) for the exact
statements, external-source review, and distinction between completed
proofs and the remaining analytic obligation.

## Hybrid product pilot

The [hybrid pilot](HYBRID_PRODUCT_PILOT.md) finds a numerical candidate
using 500,000 selected positive critical-line zeros and finite prime sums
through 2e10. A new kernel-checked positive-moment subtraction theorem
removes the need for a complete zero count or finite RH verification.
The zero boxes, finite sieve/log certificates, constant enclosures and
analytic bridge remain unproved. This is numerical feasibility, not a
completed small-endpoint product or an improved final Chen cutoff.