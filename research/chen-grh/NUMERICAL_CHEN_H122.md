# Complete Chen theorem below H = 12.2

The exact cutoff is

$$
N_0=3^{180000}<\exp(\exp(12.2)),\qquad
\log\log N_0\approx12.19475995749.
$$

For every even natural number $N\ge N_0$, `ChenEffective.GRH122.chen_explicit`
in [AuditGRH122Chen.lean](AuditGRH122Chen.lean) gives a prime plus a prime or
a product of two primes. Its `original_chen` corollary has exactly the
original `Goldbach.ChenTheorem` type. Full Dirichlet GRH remains the sole
added axiom beyond Lean's standard axioms. No `native_decide` or new
external dependency is used.

## Actual counting estimates

Write $L=\log N$ and $M(N)=\mathfrak S(N)N/L^2$. The complete proof gives

$$
W(N)\ge2.01875M(N),\qquad T(N)\le4.006M(N),
$$

and therefore

$$
R(N)\ge W(N)-\tfrac12T(N)\ge0.01575M(N)>0.
$$

The exact natural cutoff implies $L\ge197000$. The estimates apply to the
actual counts; no lower-count or triple-count hypothesis remains unproved.

## Cheap constant cleanup

[GRHJointBounds.lean](GRHJointBounds.lean) keeps the arithmetic in the
existing distribution constants instead of rounding repeatedly to powers
of ten. It proves

$$
C_5\le30000000,
$$

replacing the previous $10^{12}$ cap. This improvement needs no GRH.
The lower source-product threshold is bounded by $3^{110010}$ instead of
$3^{200010}$. The upper mass uses $r=4400$, whose threshold $3^{176001}$
is below the target and whose error still fits the $3/200$ allowance.
The lower source-mass parameter remains $r=20000000$.

The eleventh-log-power payment in the square remainder now uses a direct
proved inequality instead of requiring the oversized `logPowerCutoff 110`.
The generic logarithmic gates are restricted to the degrees used here.

## Compensated medium-prime estimate

Let $F$ be the upper linear-sieve factor and $B$ its Mertens normalization.
The new elementary estimate is

$$
B\bigl(F(s)-F(t)\bigr)\le\frac{40(t-s)}{st}
\qquad(3/2\le s\le t\le4),
$$

replacing 50. The proof retains monotonicity of the auxiliary integral
divided by its endpoint, rather than bounding the integral independently.
The actual medium-prime assembly uses this inequality and fresh rational
64-cell kernel and hat bounds. Every cell is checked in Lean. Its total
allowance remains 1.11 despite the larger geometric shift.

## Moments and joint parameters

[GRH122Moments.lean](GRH122Moments.lean) uses 148 cumulative-theta intervals.
Mixed powers of two and three give finer logarithm lower bounds, and each
rounded rational step is kernel checked. The root moment is at most 465;
the reciprocal and density divisor moments are at most $e^{465}$ and
$e^{476}$, improving $e^{500}$ and $e^{512}$ without prime enumeration.

The selected pre-sieve truncation and distribution gap are

$$
C=\lfloor N^{31/5000}\rfloor,\qquad \delta=1/400.
$$

The combined geometric shift is bounded by $11/125$. The full tail obeys

$$
336L^6\exp\!\left(476+\tfrac12\log2-\frac{31L}{10000}\right)
\le10^{-12}\qquad(L\ge197000).
$$

The pre-sieve starting endpoint stays at four million. Existing finite
prime-count, logarithm, prefix, and grid certificates are reused.

## Application-specific GRH distribution

The proved maximal prime-AP error retains the exponent $501/1000$. Summing
it with the actual squarefree divisor weight through level $N^{199/400}$
now saves $N^{-3/2000}$, rather than $N^{-1/1000}$. Its payment is

$$
3.2\times10^{17}L^7e^{-3L/2000}\le10^{-12}.
$$

The primitive and principal moving inputs from the earlier strong GRH
proof remain available for $L\ge10000$. The convolution-level condition
is now $39\log L\le L/400$. No AP or convolution estimate is assumed as
another axiom.

The Selberg radius uses $\varepsilon=1/400$, denominator coefficient
$K=8.041$, and floor reserve $1/120000$. The full triple estimate gives

$$
T(N)\le\left(8.041\cdot0.498+\frac1{1000}+\frac1{5000}\right)M(N)
<4.006M(N).
$$

## Parameter study and verification

[StudyGRHJointBudget.mjs](tools/StudyGRHJointBudget.mjs) and
[JOINT_PARAMETER_STUDY.json](JOINT_PARAMETER_STUDY.json) retain the numerical
exploration. They are explicitly not Lean proofs; their exploratory rows
do not certify all interface gates. The complete theorem uses only the
separately proved bounds in [GRH122Analytic.lean](GRH122Analytic.lean).

The final [kernel dependency audit](AuditGRH122Chen.lean) checks the exact
original statement, the transitive axiom closure, and absence of unsafe,
placeholder, and native compiler-trust proof dependencies. The
[source/object report](FINAL_GRH122_CHEN_AUDIT.json) records provenance.
No independent comparator or alternative-kernel check is claimed here.

```powershell
$env:CHEN_BUILD_TAG = 'grhtwentytwo'
$env:CHEN_BUILD_JOBS = '1'
$env:CHEN_LEAN_MEMORY_MB = '10000'
node --expose-gc --max-old-space-size=4096 OpenAI/tools/build-source.mjs AuditGRH122Chen
node research/chen-grh/tools/AuditCompletedGRH122Chen.mjs (Get-Location).Path
node OpenAI/tools/audit-sources.mjs --dirichlet-proved
```

No new large certificate campaign is required. The initial source build of
the existing certificate campaign took **15+ hours** on the development
machine. Full certificate-inclusive Chen audits have used roughly
**20–22 GiB of private committed memory for Lean alone**. Checked artifacts
are reused only after source/object and dependency provenance validation.

The previous H < 12.5 and older complete theorems and audits remain available.
