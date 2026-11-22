# Complete Chen theorem below H = 13.37

The explicit cutoff is

$$
N_0=3^{580000}<\exp(\exp(13.37)),
\qquad \log\log N_0\approx13.36483121014.
$$

For every even natural number $N\ge N_0$, there are primes $p$ and
either a prime $q$ or two primes whose product is $q$, with $N=p+q$.
The exact-cutoff theorem is `ChenEffective.GRH1337.chen_explicit` in
[AuditGRH1337Chen.lean](AuditGRH1337Chen.lean). The `original_chen` theorem
has literally the original `Goldbach.ChenTheorem` type.

This conclusion permits a square of a prime as the semiprime summand. The
sthubbar Chen entry states H = 13.375 for a square-free summand and takes four
additional analytic inputs. Its November 5 update records a fixed-level versus
all-level sieve-input issue, without changing the cutoff. These are different
formal endpoints; comparing their H values does not assert identical conclusions.
See [that entry's statement](https://github.com/sthubbar/goldbach-lean/blob/main/entries/bordignonstarichkova2024grh/ChallengeBordignonStarichkova2024GRH.lean)
and [its sieve-input note](https://github.com/sthubbar/goldbach-lean/blob/main/entries/bordignonstarichkova2024grh/NOTE-sieve-input.md).

The proof uses full Dirichlet GRH as its sole added axiom. It uses the
statement of Alpöge's announced development to avoid compiling that large
development here. This repository's local proof is relative to that axiom;
linking a checked proof of the same statement would discharge it. No numerical,
sieve, distribution, lower-count, or triple-count estimate remains assumed.

## Complete counting budget

Write

$$
L=\log N,\qquad M(N)=\mathfrak S(N)\frac{N}{L^2}.
$$

The actual counts satisfy

$$
W(N)\ge2.02575M(N),\qquad T(N)\le4.0002M(N).
$$

The corrected finite counting bridge gives

$$
R(N)\ge W(N)-\tfrac12T(N)
\ge0.02565M(N)>0.
$$

These are bounds for the actual source candidates and medium-prime aggregate,
and the complete corrected triple penalty, not substitutes for those counts.

## Changes that make the smaller cutoff possible

1. **Sharper pre-sieve moments.** Separate logarithm bounds on five prime
   intervals prove
   $$
   \sum_{p\le4000000}p^{-1/2}\le1173.
   $$
   The squarefree reciprocal and density divisor moments are bounded by
   $e^{1173}$ and $e^{1468}$, replacing $e^{1700}$ and $e^{2126}$.
   With $C=\lfloor N^{1/200}\rfloor$, the complete medium-tail envelope obeys
   $$
   336L^6\exp(1468+\tfrac12\log2-L/400)\le10^{-12}
   \quad(L\ge637000).
   $$
   The compensated expression is paid directly, without an intermediate
   exponential decay rate that would force the old cutoff.

2. **Source mass.** The upper mass error improves from $300/r$ to
   $187.5/r$, using $e^{-\gamma}\le5/8$. Choosing $r=14000$ preserves
   the existing $3/200$ allowance and replaces the hidden requirement
   $N\ge3^{800001}$ by a requirement below the new target.

3. **Distribution.** The high-conductor geometric inequalities and low scalar
   payments are proved directly at the new target. The moving endpoint only
   needs the specialized bound
   $$
   A L^k e^{-\alpha L}\le1,
   \quad A\le10^{17},\ k\le73,\ \alpha\ge1/512,
   \quad L\ge637000.
   $$
   The weighted AP estimates retain distribution level $N^{0.498}$.

4. **Numerical integration.** The medium-prime integral uses 65,000 cells and
   allowance $13/2000$. Its complete aggregate allowance remains $1.11$.
   The width-sensitive prime-pair grid retains its symbolic 200,000-cell mesh;
   it does not enumerate a quadratic grid in the kernel. The proxy coefficient
   is at most $0.49784$; including the genuine logarithmic-integral remainder
   gives the main coefficient $0.498$.

5. **Complete square and triples.** The Selberg denominator coefficient remains
   $K=8.0323$, at radius $\varepsilon=1/500$. The full square remainder is
   at most $8\cdot10^{-6}M(N)$, and the complementary triple residual is at
   most $M(N)/16000$. Thus
   $$
   T(N)\le\left(8.0323\cdot0.498+\frac1{125000}
     +\frac1{16000}\right)M(N)<4.0002M(N).
   $$

The analytic components are grouped in
[GRH1337Analytic.lean](GRH1337Analytic.lean) to avoid repeatedly loading the
common analytic environment. Four source-product/mass modules are retained
separately. The completed prime-count and logarithm certificates are reused;
no new finite certificate campaign is required.

## Reproduction and audit

With the repository's pinned Lean and Mathlib versions, set `CHEN_BUILD_TAG`
to `grh1337`, `CHEN_BUILD_JOBS` to `1`, and `CHEN_LEAN_MEMORY_MB` to `8192`.
Then run:

```sh
node --expose-gc OpenAI/tools/build-source.mjs AuditGRH1337Chen
node research/chen-grh/tools/AuditCompletedGRH1337Chen.mjs .
node OpenAI/tools/audit-sources.mjs --dirichlet-proved
```

The final native audit checks the transitive proof dependencies of the lower
and triple estimates, the exact cutoff, the Chen theorem, and the original
implicit statement. It permits only `propext`, `Classical.choice`, `Quot.sound`,
and `ChenEffective.GRH.alpoge_dirichlet_grh`. It rejects placeholders, unsafe
proof dependencies, and native compiler trust. Source/object receipts are in
[FINAL_GRH1337_CHEN_AUDIT.json](FINAL_GRH1337_CHEN_AUDIT.json).

No new package dependencies or toolchain changes are needed. A fresh build of
the existing full finite certificates still takes 15+ hours on the development
machine; their checked local artifacts can be reused. The largest serial
imports/audits have required about 20–22 GiB of private committed memory.
