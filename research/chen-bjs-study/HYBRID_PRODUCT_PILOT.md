# Hybrid product pilot: numerically viable, not a completed proof

The pilot finds a concrete route compatible with the existing near-H=30
component budgets. It does not prove a new Chen cutoff or the missing
small-endpoint product estimate. The complete Chen theorem remains at
`3^(3^134)`, H approximately 147.308095.

## Recommended candidate

Use `U=4,000,000`, a finite prime-sum check through `X=20,000,000,000`, and
500,000 selected positive critical-line zeros (plus their conjugates).
The proposed zero boxes end near height 319387.21931.

The analytic inputs to certify are

\[
 C_\xi=2+\gamma-\log(4\pi)\le0.046192,\qquad
 K_H\ge0.0461796,\qquad A_H\le19.
\]

Here H is a finite set of actual xi divisor-zero indices, including
multiplicity, and

\[
 K_H=\sum_{\rho\in H}\Re\left(\frac1\rho+\frac1{1-\rho}\right),\qquad
 A_H=\sum_{\rho\in H}\frac1{|\rho|}.
\]

Every selected zero must be proved to lie on the critical line, and the
selected indices must be distinct. These conditions are NOT established by
the downloaded numerical table. No completeness of H is needed.

## A proved improvement: completeness is unnecessary

`BJSHybridZeroKernel.lean` proves, throughout the existing 7/8 zero strip,

\[
 \frac1{|\rho(\rho+1)|}
 \le\frac32\Re\left(\frac1\rho+\frac1{1-\rho}\right).
\]

This improves the previous factor 2. Combining it with the already proved
positive Hadamard moment identity, `BJSHybridMomentResidual.lean` proves

\[
 W_H:=\sum_{\rho\notin H}\frac1{|\rho(\rho+1)|}
 \le\frac32(C_\xi-K_H).
\]

Omitted low zeros, possible omitted off-line zeros and unused multiplicity
are all included in this residual. Thus this route needs neither a
complete zero count nor finite RH through a prescribed height. In
particular, Turing completeness and an explicit zero-count tail theorem
are not premises of this residual estimate.

The exact scalar adapter `proposed_head_pays_residual` proves that the
displayed proposed caps imply

\[
 W_H\le19\cdot10^{-6}.
\]

The caps themselves remain obligations. The general residual theorem and
the scalar implication are kernel checked with only the existing local
Dirichlet axiom plus standard Lean axioms.

## Analytic envelope derived for the pilot

The following analytic applications are mathematical derivations evaluated
by the pilot; they have NOT yet been formalized in Lean.

Put L=log x and

\[
 \delta=2.02\sqrt{W_H}\,x^{-1/16}.
\]

Split the existing psi1 explicit formula into the selected critical-line
head and its remaining zeros. Finite differences cancel the constant
residue exactly. For delta <= 0.01 and x(1-delta)>1, the proposed bound is

\[
 \frac{|\psi(x)-x|}{x}
 \le1.005A_Hx^{-1/2}+2.02\sqrt{W_H}x^{-1/16}
       +2/x+2/(\delta x^2).
\]

The finite head derivative uses |x^rho/rho| <= sqrt(x)/|rho|. The remaining
psi1 term has absolute bound W_H*x^(15/8). On the upper difference,
`(1+delta)^(15/8)<=1.0201`. `smoothing_scalar` checks the resulting scalar
allocation in Lean.

For the integrated error, set

\[
 F(t)=\psi_1(t)-t^2/2,\qquad f(t)=\frac{\log t+1}{t^2\log^2t}.
\]

The split moment gives

\[
 |F(t)|\le0.12t^{3/2}+W_Ht^{15/8}+2t+10^9.
\]

Integration by parts uses F'=psi-id almost everywhere. A summand c*t^r
contributes at most c*x^(r-2)*a_r(L), where

\[
 a_r(L)=\frac1L+\frac1{L^2}
       +\frac{2/L+3/L^2+2/L^3}{2-r}.
\]

In particular,

\[
 a_{3/2}(L)=5/L+7/L^2+4/L^3,\qquad
 a_{15/8}(L)=17/L+25/L^2+16/L^3.
\]

The scalar identities are checked in Lean. This simpler integration route
does not need the incomplete-gamma machinery of the 2026 Mertens paper.
It preserves the x^(-1/8) decay in the integrated remainder rather than
integrating an unsmoothed x^(-1/16) error envelope.

`prime_power_gap_seventeen` proves psi(x)-theta(x)<=17*sqrt(x) from Mathlib.
Its combined endpoint and integral contribution is

\[
 17(3/L+2/L^2)x^{-1/2}.
\]

The proposed total prefix-error envelope is therefore

\[
 \begin{split}
 P(x)={}&[1.005A_Hx^{-1/2}+2.02\sqrt{W_H}x^{-1/16}
                  +2/x+2/(\delta x^2)]/L\\
 &+0.12a_{3/2}(L)x^{-1/2}+W_Ha_{15/8}(L)x^{-1/8}\\
 &+2a_1(L)x^{-1}+10^9a_0(L)x^{-2}
       +17(3/L+2/L^2)x^{-1/2}.
 \end{split}
\]

With A_H=19 and W_H=19e-6, the floating feasibility evaluation at X gives

| Contribution | Size |
| --- | ---: |
| Remaining-zero pointwise term | 8.42981e-5 |
| Prime-power conversion | 1.56314e-5 |
| Selected-head pointwise term | 5.69257e-6 |
| Remaining-zero integrated term | 7.46940e-7 |
| Selected-head integrated term | 1.89683e-7 |
| Other terms combined | below 2e-11 |
| Total | 1.06558618e-4 |

This is below 1/9000=1.11111111e-4. All positive terms decrease for x>=X,
and the smoothing gate improves; delta(X) is about 0.00199946. Formal
uniform scalar payment remains open; the general actual finite analytic
bridge is now proved (see HYBRID_BRIDGE_STATUS.md).
The numerical pilot is not their substitute.

## The finite prime-sum computation

`hybrid-pilot/HybridGridScan.mjs` processes all primes through 2e10 with a
segmented sieve. At scale S=2^48 it accumulates floor(S/p) exactly, so that
the reciprocal sum lies between Q/S and (Q+pi(x))/S. Integer quotient
checks and safe-integer bounds are enforced during generation.

The scan reports pi(2e10)=882,206,716 and a final reciprocal rounding width
of 3.13423e-6. This sieve computation is NOT kernel verified.

A grid with next endpoint `a+floor(a/4000)` uses 34,077 points. On [a,b],
monotonicity of the reciprocal prefix and of log log gives

\[
 R(a)-\log\log b-B_{\rm upper}\le E(x)
 \le R(b)-\log\log a-B_{\rm lower}.
\]

The generator uses exact BigInt rational bounds for both logarithms:
range reduction and 16 terms of the atanh series, with a geometric tail.
It proposes only the coarse constant enclosure

\[
 0.26149\le B_1\le0.26151.
\]

Conditional on that enclosure and correctness of the algorithms, the grid
reports the all-real finite-range enclosure

\[
 -2.52426\cdot10^{-5}\le E(x)\le6.62014\cdot10^{-5}
 \quad(4\cdot10^6\le x\le2\cdot10^{10}).
\]

The logarithm algorithm, B1 enclosure, sieve and grid rows still need Lean
proofs/checking. Exact-integer generation is not kernel certification.
The reproducible untrusted grid certificate is about 1 MB compressed.
`ValidateHybridPilot.mjs` checks its hash, coverage, interval arithmetic,
scalar budgets, and agreement with the separate per-prime scan. Its
floating-log cross-check is only an additional debugging check.

## Why the product budget closes

`BJSHybridProductBridge.lean` proves that a uniform bound |E(x)|<=1/9000
on [4e6,3^120], together with the existing proved tail, implies the actual
Goldbach relative product with tolerance 1/4000. The endpoint convention
and the local-factor correction are included.

The key scalar payment is now proved in Lean:

\[
 \exp(2/9000+24/3999999)\le1+1/4000.
\]

It uses exp(t)<=1/(1-t), preserving the first-order constant. This permits
a weaker symmetric prefix target than the old 1/20000 or proposed 1/17000.
The rounded certified product budget would be about 2.28249e-4; directly
substituting the candidate analytic envelope gives about 2.19142e-4.

The full product theorem is still conditional on `HybridPrefixWindow`.
No proof of that proposition is claimed.

## Zero-data provenance and trust boundary

The exploratory ordinates come from Andrew Odlyzko's public
[zero tables](https://www-users.cse.umn.edu/~odlyzko/zeta_tables/index.html),
file `zeros6.gz`, which advertises the first 2,001,052 zeros with accuracy
4e-9. The proposed boxes use radius 1e-6. The compressed input SHA256 is
`6acacb4707c429bf368f32823a8eef0e0737b6318d3e144c78975a4986d155da`.

These tables propose boxes; they prove no Lean zero-existence statement.
The raw table is not vendored in the Lean repository and no library
dependency or OpenAI import was added. Finite-head summaries retain the
source URL and hash. For the first 500,000 positive rows, the exploratory
head moment is above 0.0461796186 and the derivative sum is below 18.65446.

The idea of handling the integrated error separately is consistent with
[Broadbent et al. (2026), Proposition 13](https://arxiv.org/html/2608.01498v1#S2).
No theorem or numerical table from that paper was assumed or imported.

## Next proof work, in order

1. The selected-head decomposition, finite-difference estimate and actual
   integrated psi1-to-Mertens bridge are now proved and audited. Complete
   the optimized uniform numerical payment against that theorem.
2. Prove the coarse C_xi and B1 enclosures and the uniform scalar payment.
3. Benchmark a certified critical-line sign-change checker on a small
   batch, then scale to 500,000 disjoint boxes if its cost is acceptable.
   Only zero existence is needed; completeness and simplicity are not.
4. Benchmark the verified segmented-sieve / reciprocal-sum checker and
   rational logarithm checker; then check the finite grid.
5. Discharge `HybridPrefixWindow`, transport the product profile to the
   actual pre-sieved sequences, and finish the near-30 lower-count assembly.

Certifying half a million zero boxes and the large sieve computation is
substantial work. The measured JS runtime does not predict Lean kernel
checking time. The pilot establishes numerical feasibility, not a small
formalization workload.

## Verified components and reproduction

Five Lean modules compile with warnings treated as errors:
`BJSHybridPrimePowers`, `BJSHybridZeroKernel`, `BJSHybridMomentResidual`,
`BJSHybridProductBridge`, and `AuditBJSHybridPilot`. The residual audit
traverses 60,507 constants with exactly Dirichlet plus standard axioms.

The scripts use Node built-ins only. From `hybrid-pilot`, place the
untrusted downloaded `zeros6.gz` under the name
`hybrid-odlyzko-zeros6.gz`, then run:

```
node HybridMomentScan.mjs
node HybridProductPilot.mjs hybrid-product-pilot.json
node HybridPrimeScan.mjs 100000000 hybrid-prime-scan-1e8.json
node HybridPrimeScan.mjs 10000000000 hybrid-prime-scan-1e10.json
node HybridPrimeScan.mjs 20000000000 hybrid-prime-scan-2e10.json
node HybridGridScan.mjs 100000000 hybrid-grid-scan-1e8
node HybridGridScan.mjs 20000000000 hybrid-grid-scan-2e10
node ValidateHybridPilot.mjs
```

No numerical script output is imported into any Lean proof.

