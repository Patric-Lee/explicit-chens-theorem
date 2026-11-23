# Strong GRH moving-quotient estimates

This completes the stronger low-conductor moving input proposed after the
H < 13 release. The proof is in
[AuditGRHStrongMoving.lean](AuditGRHStrongMoving.lean), namespace
`ChenEffective.GRHStrongMoving`.

The standalone audit below records the input as first checked at the
H < 13 cutoff 3^400000. It has since been propagated into the
[complete H < 12 theorem](NUMERICAL_CHEN_SUB12.md), at 3^145000. Its original
audit report is retained as a historical record of the input check.

## Uniform prime-character prefixes

For every nonprincipal Dirichlet character, primitive or imprimitive, and
natural $t$ with $\log t\ge10$, the proof gives

$$
\left|\sum_{p\le t}\chi(p)\right|
\le10^{15}(\log q+\log t)^2t^{501/1000}.
$$

The underlying von Mangoldt estimate is made uniform over all prefixes,
including small prefixes treated by elementary bounds. Finite Abel
summation and the explicit prime-power correction give the actual prime
sum. No auxiliary condition $q\le\log^C t$ is needed for this theorem.

## Moving quotients and scalar payment

Write $L=\log N$ and $t=\lfloor N/a\rfloor$. For $L\ge10000$ and
$1\le a\le N^{2/3}$, the proof retains

$$
t\ge N^{3/10},\qquad \log t\ge\frac3{10}L.
$$

Consequently,

$$
t^{501/1000}
=t\exp\left(-\frac{499}{1000}\log t\right)
\le t\exp\left(-\frac{1497}{10000}L\right).
$$

For every $A\le10^{20}$ and natural $k\le80$, the scalar payment is

$$
AL^k\exp\left(-\frac{1497}{10000}L\right)\le1
\qquad(L\ge10000).
$$

The old moving argument used $t^{127/128}$ and the weaker saving
$\exp(-3L/1280)$. Neither is used in the new moving proof.

For $q\le L^b$, $b\le40$, and primitive nonprincipal $\chi$, the actual
moving prime sum satisfies

$$
\left|\sum_{p\le\lfloor N/a\rfloor}\chi(p)\right|
\le\frac{N}{aL^s}\qquad(s\le72).
$$

The principal input, centered at the real quotient rather than its floor,
satisfies

$$
\left|\pi(\lfloor N/a\rfloor)
-\operatorname{Li}_{2/\log2}(N/a)\right|
\le\frac{N}{aL^s}\qquad(s\le70).
$$

## Production aggregation and scope

Theorems `pan_low_of_log` and `pan_principal_of_log` connect these inputs to
the actual Pan low-conductor and principal aggregate definitions. They pay
the source-variable summation, prime-deletion, cofactor, and harmonic costs
for $L\ge10000$, saving degree at most 32 and low-conductor log degree at
most 38, with coefficient 4 as in the previous production bounds.

`numerical_pan_ledger` combines the new low input with the already proved
high-conductor input at the current Chen cutoff. Its type is checked to be
definitionally equal to the previous production cofactor-ledger theorem's
type. The full high-conductor threshold has not been reduced here.

The focused dependency audit rejects the old weak moving lemmas and the
old low-conductor and cofactor-ledger theorems in the new proof's dependency
closure. It allows only full Dirichlet GRH and Lean's standard axioms;
`sorry`, native compiler trust, and unsafe proof dependencies are rejected.
The source/object report is [STRONG_MOVING_AUDIT.json](STRONG_MOVING_AUDIT.json).
No package or toolchain pin has changed. No new finite certificate campaign
is needed.

This is a repository-local audit. The independent comparator, sandboxed
rebuild, and alternative-kernel checks discussed separately have not been
run for this development.

## Reproduction

```powershell
$env:CHEN_BUILD_TAG = 'strongmoving'
$env:CHEN_BUILD_JOBS = '1'
$env:CHEN_LEAN_MEMORY_MB = '10000'
node --expose-gc --max-old-space-size=4096 OpenAI/tools/build-source.mjs AuditGRHStrongMoving
node research/chen-grh/tools/AuditStrongGRHMoving.mjs (Get-Location).Path
node OpenAI/tools/audit-sources.mjs --dirichlet-proved
```

The next cutoff bottlenecks are the pre-sieve tail and the fixed Selberg
square-error allowance, both near $L=400000$ in their current forms. Their
joint improvement is a separate step.
