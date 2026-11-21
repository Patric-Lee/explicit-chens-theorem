# Explicit Chen existence below H = 14

Assuming full Dirichlet GRH as the sole additional axiom, the released theorem
`ChenEffective.GRH14.chen` states that every even natural number

\[
N\ge N_*=3^{1,000,000}<\exp(\exp(14))
\]

is a prime plus either a prime or a product of two primes. The logarithmic
height of the exact cutoff is approximately 13.909558. This is a qualitative
existence result; the older 0.67 counting theorem keeps its larger cutoff.

The statements and semantic audit are in
[AuditGRH14Chen.lean](AuditGRH14Chen.lean), re-exported by
[GRH14Chen.lean](GRH14Chen.lean). The `original_chen` corollary has literally
the original `Goldbach.ChenTheorem` type, and its proof uses the new explicit
theorem. The earlier implicit Chen theorem is therefore recovered by this route.

## Complete numerical budget

Let

\[
M(N)=\mathfrak S(N)\frac{N}{\log^2N}.
\]

The already audited lower-count proof gives the actual weighted count

\[
W(N)\ge2.02575M(N).
\]

The new upper proof gives the actual corrected triple penalty

\[
T(N)\le3.993M(N).
\]

The finite counting bridge then yields

\[
R(N)\ge W(N)-\tfrac12T(N)\ge0.02925M(N)>0.
\]

The bridge concerns the actual representation set, and includes the
non-reduced cases, source endpoints, and proper-prime-power corrections.

## Prime-pair main term

The reciprocal-prime interval error is \(e=100/\log^2N\). Retaining the
widths of logarithmic rectangles changes the grid error from a fixed error
per cell to

\[
30ne+5n^2e^2.
\]

For \(n=200000\), the symbolic quadrature theorem has mesh loss at most
\(759/n=0.003795\), and the interval-error contribution is at most
\(0.000601\). Together with the proved source integral below \(0.49254\),
this gives the prime-pair proxy at most \(0.49694\). The genuine logarithmic
integral correction is then included to obtain

\[
\text{actual Li main sum}\le0.4971\frac{N}{\log N}.
\]

This is a symbolic finite-sum comparison, not a computation over the grid's
individual cells. The numerical grid size stays behind a proved opaque
certificate while the mesh and scalar error inequalities use its value.

## Complete distribution remainder

The moving quotient \(t=\lfloor N/a\rfloor\), with \(a\le N^{2/3}\),
satisfies \(\log t\ge\tfrac14\log N\). For \(b\le40\), the conductor
comparison uses

\[
q\le(\log N)^b\le(\log t)^{2b},
\]

avoiding the earlier exponential threshold in \(b\). Existing numerical
character power bounds and the GRH principal estimate supply the low and
principal lanes; the proved high-conductor large-sieve argument is retained.

Writing \(L=\log N\), the explicit payment

\[
\log L\le L/60000,\qquad
A L^k e^{-\alpha L}\le1
\quad(A\le10^{20},\ k\le100,\ \alpha\ge1/512)
\]

holds for \(L\ge10^6\). It makes the low and principal ledger constants
numerical without an eventual threshold. The weighted Pan estimate uses
order five and logarithmic modulus exponent 38. The required source level
is included because

\[
N^{0.498}\le\frac{\sqrt N}{(\log N)^{39}}.
\]

The literal source-window restriction, Li-normalization correction, and
non-coprime R1 correction are all included. For the optimal Selberg weights,
the resulting complete remainder satisfies

\[
|\mathcal R(N)|\le10^{12}\frac{N}{\log^5N}
\le\frac1{500000}M(N).
\]

With sieve radius parameter \(\varepsilon=1/500\), the previously proved
denominator coefficient 8.0323 therefore gives

\[
\text{Selberg square count}
\le\left(8.0323\cdot0.4971+\frac1{500000}\right)M(N).
\]

The square-to-triple residual is at most \(M(N)/20000\); this proves the
stated triple coefficient 3.993.

## Audit and reproduction

[FINAL_GRH14_CHEN_AUDIT.json](FINAL_GRH14_CHEN_AUDIT.json) records the
source/object provenance and the successful native Lean semantic audit.
The audit checks the explicit theorem, literal original-statement recovery,
and the cutoff below double exponential height 14. Only full Dirichlet GRH
and Lean's standard axioms are permitted. There is no `sorry`,
`native_decide`, unsafe proof, or additional package dependency.

```powershell
$env:CHEN_BUILD_TAG = 'grhstrip'
$env:CHEN_BUILD_JOBS = '1'
node --expose-gc OpenAI/tools/build-source.mjs AuditGRH14Chen
node research/chen-grh/tools/AuditCompletedGRH14Chen.mjs $PWD
```

The existing finite certificates are reused. Their documented 15+ hour
first build and memory requirements still apply to a fresh build. This
upper-bound improvement introduces no new large finite computation. The
final certificate-inclusive audit should be run serially; earlier full
checks used around 20–22 GiB of Lean private memory, plus build-runner and
system memory. The assumed external GRH proof is not imported or rebuilt.
