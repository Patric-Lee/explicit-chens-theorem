# Complete Chen theorem below H = 12

The exact cutoff is

$$
N_0=3^{145000}<\exp(\exp(12)),\qquad
\log\log N_0\approx11.97853684902.
$$

For every even natural number $N\ge N_0$, `ChenEffective.GRHSub12.chen_explicit`
in [AuditGRHSub12Chen.lean](AuditGRHSub12Chen.lean) gives a prime plus a prime
or a product of two primes. Its `original_chen` corollary has exactly the
original `Goldbach.ChenTheorem` type.

Full Dirichlet GRH remains the sole added axiom beyond Lean's standard
axioms. All numerical, lower-sieve, distribution, and triple-count inputs
are proved. No `native_decide` or new external dependency is used.

## Complete counting budget

Write $L=\log N$ and $M(N)=\mathfrak S(N)N/L^2$. The actual counts satisfy

$$
W(N)\ge2.01025M(N),\qquad T(N)\le4.010M(N).
$$

The corrected finite counting bridge gives

$$
R(N)\ge W(N)-\tfrac12T(N)\ge0.00525M(N)>0.
$$

The exact natural cutoff implies $L\ge159000$. The proof does not assume
the approximate double logarithm printed above.

## Kernel-certified prime moments

[GRHMomentCounts.lean](GRHMomentCounts.lean) imports 148 prime-count
certificates under [GRHMomentCertificates](GRHMomentCertificates).
They use the existing minimal bit-packed sieve from the local calr3 port.
Each file checks both the prime-count packing and its total with
`decide +kernel`. The generated JavaScript data is not trusted.

The certificates cover consecutive square-endpoint intervals from 100 to
four million. Each count includes at most 31 integers of endpoint padding;
this enlarges an upper bound safely. The soundness theorem in
[GRHMomentCountSoundness.lean](GRHMomentCountSoundness.lean) proves that
the packed counts count actual primes and dominate every relevant prime
subset. For each interval with lower endpoint $r_i^2$, the moment is at
most $c_i/r_i$.

The small-prime bound and directed rational accumulation give

$$
20+\sum_i\frac{c_i}{r_i}\le\frac{3372269}{10000}<340.
$$

Every accumulation step is checked in
[GRHSub12Moments.lean](GRHSub12Moments.lean). Thus

$$
\sum_{p\le4000000}\frac1{\sqrt p}\le340.
$$

The existing local-density comparison then gives

$$
1.01\cdot340+\tfrac14\cdot20+1=349.4<350.
$$

The reciprocal and density divisor moments are therefore at most
$e^{340}$ and $e^{350}$, replacing $e^{465}$ and $e^{476}$. These moment
theorems use only standard Lean axioms; they do not require GRH.

[GRHMomentCertificateData.json](GRHMomentCertificateData.json) contains
the generated proposals and source hashes. Their checked provenance is
recorded separately in the final audit report.

## Joint parameters and source mass

The proof selects

$$
C=\lfloor N^{29/5000}\rfloor,\qquad
\delta=3/1000,\qquad D\le N^{497/1000}.
$$

The lower-sieve geometric shift is bounded by $89/1000$. The complete
pre-sieve tail is paid directly:

$$
336L^6\exp\!\left(350+\tfrac12\log2-\frac{29L}{10000}\right)
\le10^{-12}\qquad(L\ge159000).
$$

The upper source mass uses $r=3300$ and allowance $1/50$. Its threshold
$3^{132001}$ is below the target. The lower source parameter remains
$r=20000000$, with source-product threshold at most $3^{110010}$.

The compensated medium-prime bound with shift constant 40 is retained.
Fresh rational 64-cell bounds support aggregate allowance 1.135. The base
and endpoint allocations are 0.063 and 1/20000 respectively, giving

$$
2.6408-0.063-\tfrac12(1.135)-1/20000=2.01025.
$$

## GRH distribution and complete triples

The proved maximal prime-AP error retains exponent $501/1000$. At the
selected level $N^{497/1000}$, the actual squarefree weighted sum saves
$N^{-1/500}$. Its numerical payment is

$$
3.2\times10^{17}L^7e^{-L/500}\le10^{-12}.
$$

The convolution-level condition is $39\log L\le3L/1000$. The logarithmic
payments use the application degrees and $\log L\le L/13000$, replacing
the previous overly restrictive common bound.

The Selberg radius is $\varepsilon=3/1000$, its denominator coefficient
is $K=8.049$, and its floor reserve is $1/100000$. The proved remainder
constant cap remains $C_5\le30000000$. The complete prime-pair main
coefficient remains 0.498. Consequently,

$$
T(N)\le\left(8.049\cdot0.498+\frac1{1000}+\frac1{4000}\right)M(N)
<4.010M(N).
$$

The pair-grid and logarithmic-integral errors, full distribution remainder,
and complementary triples are all included. The final result is assembled
in [GRHSub12Analytic.lean](GRHSub12Analytic.lean).

## Verification and reproduction

The [final Chen audit](AuditGRHSub12Chen.lean) checks the transitive axiom
closure, rejects placeholders and unsafe/native compiler-trust proof
paths, and checks literal recovery of the original Chen statement. The
[source/object report](FINAL_GRHSub12_CHEN_AUDIT.json) verifies source,
compiled-object, and recursive dependency provenance, including all 148
new moment certificates. No independent comparator or alternative-kernel
verification is claimed.

The completed Lean audit traversed **1,517,751 transitive constants**
in about **896 seconds** on the development machine. Its axiom closure is
exactly `propext`, `Classical.choice`, `Quot.sound`, and
`ChenEffective.GRH.alpoge_dirichlet_grh`.

From the repository root:

```powershell
$env:CHEN_BUILD_TAG = 'grhsubtwelve'
$env:CHEN_BUILD_JOBS = '1'
$env:CHEN_LEAN_MEMORY_MB = '10000'
node --expose-gc --max-old-space-size=4096 OpenAI/tools/build-source.mjs AuditGRHSub12Chen
node research/chen-grh/tools/AuditCompletedGRHSub12Chen.mjs (Get-Location).Path
node OpenAI/tools/audit-sources.mjs --dirichlet-proved
```

The new count sources total under 0.7 MB. The first and last interval
benchmarks took about 1.3 and 1.7 seconds; the remaining batch's checking
phase took about 83 seconds with four jobs, after ledger discovery and
reuse validation. All finite computation uses the Lean kernel. The optional
[generator](tools/GenerateSub12MomentCertificates.mjs) uses Node built-ins;
its output still requires these Lean checks.

The earlier large certificate campaign is reused. Its initial source build
took **15+ hours** on the development machine. Full certificate-inclusive
Chen audits have used roughly **20–22 GiB of private committed memory for
Lean alone**. The new small moment certificates do not replace that
existing campaign.

The previous H < 12.2 and older complete theorems and audits remain available.
