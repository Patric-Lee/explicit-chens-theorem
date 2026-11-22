# Chen's theorem with H < 13

The exact cutoff is

$$
N_0=3^{400000}<\exp(\exp13),\qquad
\log\log N_0\approx12.99326765371.
$$

The theorem `ChenEffective.GRHSub13.chen_explicit` in
[AuditGRHSub13Chen.lean](AuditGRHSub13Chen.lean) proves that every even natural
number at or above this cutoff is a prime plus a prime or a product of two
primes. Its `original_chen` corollary has literally the original
`Goldbach.ChenTheorem` type.

Full Dirichlet GRH remains the sole additional axiom. No additional sieve,
distribution, numerical, or counting result is assumed. The pinned Lean and
mathlib versions and external packages are unchanged; no `native_decide` is
used. The earlier H < 13.37 proof remains available.

## Complete counting budget

Put $L=\log N$ and $M(N)=\mathfrak S(N)N/L^2$. The actual counts satisfy

$$
W(N)\ge2.02575M(N),\qquad T(N)\le4.0004M(N).
$$

The corrected finite counting bridge therefore gives

$$
R(N)\ge W(N)-\tfrac12T(N)\ge0.02555M(N)>0.
$$

## Improvements

1. **Cumulative prime moments.** Summation by parts retains the differences
   of cumulative theta sums on eight intervals, rather than bounding each
   interval by the full theta prefix independently. This proves
   $$
   \sum_{p\le4000000}p^{-1/2}\le710
   $$
   without enumerating the primes. The reciprocal and density divisor
   moments are bounded by $e^{710}$ and $e^{889}$. For
   $C=\lfloor N^{1/200}\rfloor$, the complete truncation envelope satisfies
   $$
   336L^6\exp(889+\tfrac12\log2-L/400)\le10^{-12}
   \qquad(L\ge439000).
   $$

2. **Source mass.** For $r\ge10$, retain the small parameter $t=1/r$ in
   $(1+t)^4\le1+5t$. Together with $e^{-\gamma}\le5/8$, this replaces the
   error coefficient $187.5/r$ by $62.5/r$. Taking $r=5000$ preserves the
   existing $3/200$ source-mass allowance at a smaller threshold.

3. **Power-decaying Mertens error.** The already proved theta estimate gives
   $$
   |P(x)-\log\log x-B_1|
   \le\frac34\frac{17\log x+16}{\log^2x}x^{-1/16}
   \le\frac1{10000\log^2x}
   $$
   for $x\ge3^{120}$ and $\log x\ge1000$. At the endpoints used by the
   lower and triple counts this yields interval error $1/L^2$, replacing
   $100/L^2$. The symbolic 65,000-cell medium grid and 200,000-cell pair grid
   are reused.

4. **Moving quotients.** For $a\le N^{2/3}$, retain
   $\lfloor N/a\rfloor\ge N^{3/10}$, replacing $N^{1/4}$. The old
   $1/128$ power saving consequently pays with
   $e^{-3L/1280}$. The specialized degree-73 payment is checked directly
   for $L\ge439000$. Other log-power bounds use their actual application
   degrees rather than an unused degree-80 or degree-189 endpoint.

5. **Complete triples.** The Selberg radius is $\varepsilon=1/500$ and
   the denominator coefficient is $K=8.0325$. Retaining the proved
   prime-pair reciprocal sum bound $1/2$ reduces the genuine
   logarithmic-integral remainder from $90N/L^2$ to $45N/L^2$. The genuine
   main coefficient remains $0.498$. Finally
   $$
   T(N)\le\left(8.0325\cdot0.498+\frac1{32000}
      +\frac1{11000}\right)M(N)<4.0004M(N).
   $$

## Verification and reproduction

The analytic proof is grouped in
[GRHSub13CompleteAnalytic.lean](GRHSub13CompleteAnalytic.lean), avoiding
repeated loading of the common environment. The final audit checks the
transitive axiom closure, rejects unsafe and compiler-trust proof paths,
and checks literal recovery of the original Chen statement.

From the repository root, with Node and Git available:

```powershell
$env:CHEN_BUILD_TAG = 'subthirteen'
$env:CHEN_BUILD_JOBS = '1'
$env:CHEN_LEAN_MEMORY_MB = '10000'
node --expose-gc --max-old-space-size=4096 OpenAI/tools/build-source.mjs AuditGRHSub13Chen
node research/chen-grh/tools/AuditCompletedGRHSub13Chen.mjs (Get-Location).Path
node OpenAI/tools/audit-sources.mjs --dirichlet-proved
```

Existing finite certificates are reused. A new clone still needs the full
certificate build, which has taken **15+ hours** on the development machine.
The final audits have needed roughly **20–22 GiB of private committed memory**
for Lean alone; this is distinct from resident RAM. Adequate RAM or paging
capacity is needed. See the main README for the build and memory details.
