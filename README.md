# Explicit Chen's theorem in Lean

This project formalizes explicit cutoffs for Chen's theorem. Its best checked
result proves that every even integer at least 3^(3*10^12) is a prime plus
a prime or semiprime, assuming only Platt's modulus-one finite RH input
beyond Lean's standard axioms. The exact cutoff is below exp(exp(29)).

## Results and assumptions

| Route | Exact cutoff | Approximate H, where N₀ = exp(exp(H)) | Additional axiom beyond standard Lean |
| --- | --- | --- | --- |
| [Checked Platt-based H<29 theorem](research/chen-numerical-study/BJSH29ConditionalChen.lean) | 3^(3*10^12) | 28.82368123221 | Modulus-one finite RH through height 10^8 |
| [Checked numerical theorem](research/chen-bjs-study/BJSTightChen.lean) | 3^(3^134) | 147.308095 | None |
| [Checked Platt-based H≈30 theorem](research/chen-numerical-study/BJSH30ConditionalChen.lean) | 3^(10^13) | 30.02765403654 | Modulus-one finite RH through height 10^8 |

The best Platt-based result is **conditional**. Lean proves its exact cutoff
is strictly below exp(exp(29)). The earlier H≈30 theorem remains available.
For every even natural number N at or above its cutoff, its statement is

$$
N\ge N_0=3^{3\cdot10^{12}}
\quad\Longrightarrow\quad
\exists p,q\in\mathbb N,\quad
N=p+q,\quad p\text{ prime},\quad
q\text{ prime or a product of two primes}.
$$

The declaration is `ChenEffective.H29Conditional.chen`. See the
[H<29 budget and audit](research/chen-numerical-study/NUMERICAL_H29.md).
Its `original_chen` corollary has exactly the original
`Goldbach.ChenTheorem` type. This checks that the numerical route proves
the original existence statement. The standard-only H≈147 theorem has its
own literal recovery theorem and remains separate from the conditional route.

The sole additional axiom is the published modulus-one Platt finite-RH
statement through height 100,000,000. The former temporary reciprocal-prefix
axiom has been removed. The all-real prefix bound

$$
\left|\sum_{p\le x}\frac1p-\log\log x-B_1\right|
\le\frac1{9000}\qquad(4{,}000{,}000\le x\le3^{120})
$$

is now proved from the completed kernel-checked finite certificates and
the Platt analytic tail. There are no extra sieve-density, AP-distribution,
lower-count, triple-count or existence axioms. The final Chen audit permits
exactly the named Platt input and `propext`, `Classical.choice`, `Quot.sound`.
See the [proof assembly and audit](research/chen-platt/README.md).

## Approach

Let the singular-series main scale be

$$
M(N)=\mathfrak S(N)\frac{N}{(\log N)^2}.
$$

The proof combines actual finite candidate counts, explicit AP-distribution
estimates, a linear lower sieve, a Selberg-square/triple upper estimate, and
the exact counting implication below.

1. **Prime products and pre-sieving.** The reciprocal-prefix window and the
   proved infinite tail supply the relative Goldbach sieve product bound

   $$
   \prod_{u\le p<z}\frac{p-1}{p-2}
   \le\left(1+\frac{1}{4000}\right)\frac{\log z}{\log u},
   \qquad 4{,}000{,}000\le u\le z.
   $$

   The product is over primes; the formal adapter also handles the subsets
   and endpoint conventions used by the sieve. The standard-only route uses
   the larger start U=3^120, which explains much of its larger cutoff.

2. **Distribution and the lower count.** The proved Dirichlet seven-eighths
   theorem makes the Siegel and low-conductor inputs effective. Numerical
   weighted distribution estimates pay the actual QD remainders in the
   pre-sieved counting problem. The base and medium-prime estimates yield

   $$
   W(N)\ge2.02575\,M(N)
   \qquad\left(N\ge3^{3\cdot10^{12}},\ N\text{ even}\right).
   $$

3. **The complete triple estimate.** The two-term Selberg denominator
   expansion, prime-pair main term, fifth-order square remainder, Q residual,
   and complementary triples are assembled into

   $$
   T(N)\le
   \left[8.2\left(0.49254+\frac{1}{10000}\right)
     +\frac{1}{1000}\right]M(N)
   =4.040648\,M(N),
   \qquad N\ge3^{3\cdot10^{12}}.
   $$

   This upper estimate is proved independently of the Platt
   input. See the [complete triple result](research/chen-numerical-study/NUMERICAL_H29.md#sharper-mertens-normalization).

4. **Exact finite counting.** The representation count satisfies

   $$
   R(N)\ge W(N)-\frac{1}{2}T(N)
   \ge0.005426\,M(N)>0.
   $$

   Positivity supplies a prime plus a prime or semiprime. The exact bridges
   use the actual candidate and penalty counts, rather than assumed
   surrogates. The earlier 0.67 counting theorem retains its separate cutoff.

## Platt finite-RH input and certified prefix window

The sole additional axiom is

$$
\zeta(\rho)=0,\quad0<\Re\rho<1,\quad|\Im\rho|\le10^8
\quad\Longrightarrow\quad\Re\rho=\tfrac12.
$$

This is a finite modulus-one statement. The Dirichlet seven-eighths input is
proved separately by the vendored OpenAI development.

Writing P(x) for the reciprocal-prime sum, E(x)=P(x)−log log x−B₁ and
R=10¹⁰, the finite proof establishes

$$
|E(x)-E(R)|=|P(x)-P(R)-(\log\log x-\log\log R)|
\le\frac1{20000}\qquad(4\cdot10^6\le x\le R).
$$

It uses 76,265 checked count chunks, 937 log chunks and 239,866 grid points.
The cumulative-prefix, point/grid alignment and all-real coverage proofs
include the section boundaries. The analytic proof gives |E(x)| ≤ 59/10⁶ on
[R,3⁵¹²], and the exact budget 59/10⁶ + 1/20000 ≤ 1/9000 closes the window.
No numerical enclosure of B₁ or unverified zero table is assumed.
See [the completed integration and final audit](research/chen-platt/README.md).
No `native_decide` or new external Lake package was introduced.

The H<29 refinement retains the same counted finite window. Its variable
budget keeps the pre-sieve contraction, BV range loss and triple remainder
separate. The sharper already-proved Mertens product is used in the Pan
normalization. At L = log N ≥ 3·10¹² the certified lower count remains
2.02575 M(N), and the normalized triple error
2 C₅/L³ + 38/L is at most 0.001, with C₅ ≤ 10³⁴. No new finite campaign,
external axiom, or external package is needed.

## Build time and memory

A first build of the full finite certificates and their assembly takes
**15+ hours** on the development machine; allow longer on slower hardware or
with fewer workers. This is a planning estimate, not a guaranteed runtime.
The count campaign alone recorded about 65 hours of accumulated Lean process
time across its parallel workers. Generating the proposed data and checking
it in Lean are separate steps: committed certificate sources still have to
be kernel-checked on a source-only checkout.

The development machine had about **14 GiB usable physical RAM**. The largest
serial import/audit processes reached roughly **20–22 GiB of private committed
memory**, requiring substantial paging. These figures are not resident-RAM
measurements. **32 GiB RAM is recommended** for a smoother build; a 16 GiB
machine needs ample swap/pagefile space and can be much slower. Keep the
largest global joins and final audits serial, and reduce chunk-worker
parallelism if memory is tight. Leave room in the system commit limit for
Lean and other running applications; disabling swap on a 16 GiB machine is
not a suitable configuration for these checks.

Unchanged, locally checked artifacts can be reused by the hash-aware runners.
The Git repository does not distribute the local Lean object cache, and JSON
receipts or JavaScript results do not replace kernel checking. See the
[certificate build notes](research/chen-platt/README.md#build-time-and-memory).

## Verification and scope

The checked upgrade uses Lean 4.34.1 and Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
The [H<29 audit report](research/chen-platt/FINAL_CHEN_H29_AUDIT.json) records
the current source/object hashes, exact cutoff, axiom closure, and recovery
of the original Chen statement. The earlier
[upgrade audit](research/chen-effective/UPGRADE_434_AUDIT.md) records the
checked OpenAI proof and preceding H≈30 release.
The [OpenAI provenance and build guide](OpenAI/README.md) records the pins,
licenses, source mapping, and transitive proof audits.

Install Git, Node.js, and [elan](https://github.com/leanprover/elan). The
repository pins Lean 4.34.1. On a fresh checkout, fetch the Mathlib cache:

```sh
git clone -c core.autocrlf=false https://github.com/Patric-Lee/explicit-chens-theorem.git
cd explicit-chens-theorem
lake exe cache get
```

The focused source builder checks the numerical Chen route independently
of the broader inherited developments:

```sh
node OpenAI/tools/verify-sources.mjs
node OpenAI/tools/audit-sources.mjs --dirichlet-proved
node --expose-gc OpenAI/tools/build-source.mjs AuditBJSTightBudget AuditBJSH29Conditional OAI.AuditChenIntegration
node OpenAI/tools/build-source.mjs PlattThetaInputs PlattSegmentPilot
```

For the reproducible hash report, follow the
[H<29 audit commands](research/chen-numerical-study/NUMERICAL_H29.md#assumptions-audits-and-reuse),
which set the build tag and serial memory settings before running the final
source/object audit. The report records a completed local check; it does not
replace kernel checking on a fresh source checkout.

Standard-only routes reject custom axioms, placeholders, unsafe proof
dependencies, and native compiler trust. The conditional H<29 audit permits
only the published modulus-one Platt input. Historical studies, unfinished experiments,
and untrusted numerical scans are not silently promoted to theorem inputs.

## References, provenance, and acknowledgments

- [subfish-zhou/goldbach-lean](https://github.com/subfish-zhou/goldbach-lean):
  upstream Chen formalization and reusable analytic number theory. Its
  history, copyright notices, and Apache-2.0 license are retained.
- [OpenAI/math](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae):
  the proved Dirichlet seven-eighths input. The actual proof closure, rather
  than a challenge placeholder, is vendored under [OpenAI/](OpenAI/README.md),
  with 2,924 OAI files and 15 Rellich files, pinned manifests, and licenses.
- [calr3/ternary-goldbach](https://github.com/calr3/ternary-goldbach/tree/ab016043e852c126492310d8fc44ea7849c381b2):
  adapted finite-RH analytic estimates and minimal kernel sieve. The local
  port restricts the RH input to modulus one. Its selected checked closure,
  changes, source hashes, Apache-2.0/MIT licenses, and RSBounds provenance are
  documented in [chen-platt](research/chen-platt/README.md).
- [AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
  and [sthubbar/lean-lab-preprints](https://github.com/sthubbar/lean-lab-preprints):
  selectively adapted Hadamard-factorization, explicit-formula, and
  zero-counting proofs. See [source notices](research/chen-dusart/NOTICE.md)
  and the [pinned provenance manifest](research/chen-dusart/provenance.json).
- [teorth/IEANTN](https://github.com/teorth/IEANTN): consulted for explicit
  analytic-number-theory methods and available formal results; no complete
  port of that project is claimed.
- [gersh/ternary-goldbach-lean](https://github.com/gersh/ternary-goldbach-lean):
  consulted for finite-computation and finite-RH certificate approaches;
  its numerical assumptions are not imported as additional axioms here.
- [b-mehta/PrimeCert](https://github.com/b-mehta/PrimeCert): Bhavik Mehta and
  contributors' minimal sieve informed the earlier local certificate port.
  Its [source notices and license](research/chen-bjs-study/hybrid-pilot/primecert-port/NOTICE.md)
  are retained.
- Matteo Bordignon, Daniel R. Johnston, and Valeriia Starichkova (BJS),
  [An explicit version of Chen's theorem and the linear sieve](https://arxiv.org/abs/2207.09452):
  reference for the sharp sieve layers, recurrence, discrete induction, and
  parity bounds. This repository does not claim to reproduce their complete
  numerical application merely by using those ingredients.
- Tomohiro Yamada, [Explicit Chen's theorem](https://arxiv.org/abs/1511.03409):
  motivation and a comparison point; its claimed threshold is not assumed
  as a Lean input.
- Chen, Jurkat–Richert, Suzuki, Selberg, and Dusart supply the mathematical
  methods behind the local estimates. The Dusart-related branch proves the
  restricted conclusions it uses; it does not formalize all of Dusart's work.

The original [license](LICENSE) and adapted-source notices are retained.
