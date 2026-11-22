# Explicit Chen's theorem in Lean

This project formalizes explicit cutoffs for Chen's theorem. Its best checked
result proves that every even integer at least 3^400000 is a prime plus
a prime or a product of two primes, assuming full Dirichlet GRH as the sole
external axiom beyond Lean's standard axioms. This cutoff is below exp(exp(13)); its double logarithm is approximately 12.993268.

## Results and assumptions

| Route | Exact cutoff | Approximate H, where N₀ = exp(exp(H)) | Additional axiom beyond standard Lean |
| --- | --- | --- | --- |
| [GRH-based H<13 theorem](research/chen-grh/AuditGRHSub13Chen.lean) | 3^400000 | 12.99326765371 | Full Dirichlet GRH (Alpöge statement) |
| [GRH-based H<13.37 theorem](research/chen-grh/AuditGRH1337Chen.lean) | 3^580000 | 13.36483121014 | Full Dirichlet GRH (Alpöge statement) |
| [GRH-based H<14 theorem](research/chen-grh/AuditGRH14Chen.lean) | 3^1000000 | 13.90955838558 | Full Dirichlet GRH (Alpöge statement) |
| [GRH-based H<29 theorem](research/chen-numerical-study/BJSH29ConditionalChen.lean) | 3^(3*10^12) | 28.82368123221 | Full Dirichlet GRH (Alpöge statement) |
| [Checked numerical theorem](research/chen-bjs-study/BJSTightChen.lean) | 3^(3^134) | 147.308095 | None |
| [GRH-based H≈30 theorem](research/chen-numerical-study/BJSH30ConditionalChen.lean) | 3^(10^13) | 30.02765403654 | Full Dirichlet GRH (Alpöge statement) |

The H<13 proof is complete: no lower-count, triple-count, sieve, or numerical
estimate remains an unproved input. We use the full Dirichlet GRH statement
from Levent Alpöge's announced Lean development as the sole additional axiom,
to avoid compiling and replaying that large development here. Our local
build therefore proves Chen's theorem relative to this explicitly declared
GRH axiom; linking a checked proof of the same GRH statement would discharge
it. We do not claim that this repository has checked Alpöge's proof.
Lean proves that our exact cutoff is strictly below exp(exp(13)). The earlier
H<29 and H≈30 theorems remain available.
For every even natural number N at or above its cutoff, its statement is

$$
N\ge N_0=3^{400\,000}
\quad\Longrightarrow\quad
\exists p,q\in\mathbb N,\quad
N=p+q,\quad p\text{ prime},\quad
q\text{ prime or a product of two primes}.
$$

The exact-cutoff declaration is `ChenEffective.GRHSub13.chen_explicit`. See the
[H<13 proof, complete budget and audit](research/chen-grh/NUMERICAL_CHEN_SUB13.md).
Its `original_chen` corollary has exactly the original
`Goldbach.ChenTheorem` type. This checks that the numerical route proves
the original existence statement. The standard-only H≈147 theorem has its
own literal recovery theorem and remains separate from the conditional route.

The sole additional axiom is now full Dirichlet GRH, matching the
Alpöge/Claude release's all-moduli, all-heights critical-strip statement.
We assume that statement instead of importing its large proof. The old Platt
finite-RH declaration is now a theorem derived from GRH, not another axiom.
The former temporary reciprocal-prefix axiom has been removed. The all-real prefix bound

$$
\left|\sum_{p\le x}\frac1p-\log\log x-B_1\right|
\le\frac1{9000}\qquad(4{,}000{,}000\le x\le3^{120})
$$

is now proved from the completed kernel-checked finite certificates and
the finite-height analytic tail (its RH premise is now derived from GRH).
There are no extra sieve-density, AP-distribution,
lower-count, triple-count or existence axioms. The final Chen audit permits
exactly the named full Dirichlet GRH input and `propext`, `Classical.choice`, `Quot.sound`.
See the [proof assembly and audit](research/chen-platt/README.md).

The **H<13 existence theorem is complete and audited**. At the exact cutoff
3^400000, the actual weighted lower count has coefficient 2.02575 and the
complete corrected triple upper count has coefficient 4.0004. The exact
counting bridge leaves the positive representation margin 0.02555. The
older 0.67 counting theorem retains its larger cutoff. See the
[GRH route](research/chen-grh/README.md).
The prior Platt-only reports record historical proof snapshots.

The [smaller-cutoff budget pilot](research/chen-grh/SHARP_PILOT.md) has now been
propagated through the complete lower and triple estimates and final Chen audit.


## Approach

Write

$$
L=\log N,\qquad M(N)=\mathfrak S(N)\frac{N}{L^2}.
$$

At the exact cutoff $N_0=3^{400000}$, the complete inequalities are

$$
W(N)\ge2.02575M(N),\qquad T(N)\le4.0004M(N),
$$

and the corrected finite counting bridge gives

$$
R(N)\ge W(N)-\frac12T(N)\ge0.02555M(N)>0.
$$

1. **Prime products and pre-sieving.** The kernel-checked reciprocal-prefix
   certificates and proved analytic tail give the relative Goldbach product
   bound with allowance 1/4000 from 4,000,000 onward. Cumulative theta
   differences on eight intervals reduce the reciprocal-square-root prime
   moment to 710, and the density divisor moment to exp(889). With
   C = floor(N^(1/200)), the full truncation envelope is paid directly:

   $$
   336L^6\exp(889+\tfrac12\log2-L/400)\le10^{-12}
   \qquad(L\ge439000).
   $$

2. **Actual lower count.** The source-mass error coefficient improves from
   187.5/r to 62.5/r for r >= 10, preserving the existing 3/200 allowance
   at r = 5000. The power-decaying theta estimate gives reciprocal-prime
   interval error 1/L^2 instead of 100/L^2.
   Proved weighted AP distribution at level N^0.498, the truncated lower
   sieve, and the complete medium-prime aggregate give the stated bound on
   W(N). The medium integral uses 65,000 cells and retains the aggregate
   allowance 1.11.

3. **Complete triples.** The two-term Selberg expansion gives denominator
   coefficient K = 8.0325 at radius epsilon = 1/500. A width-sensitive,
   symbolic 200,000-cell prime-pair grid gives genuine main coefficient
   0.498. The complete distribution remainder and complementary triples give

   $$
   T(N)\le\left(8.0325\cdot0.498+\frac1{32000}
     +\frac1{11000}\right)M(N)<4.0004M(N).
   $$

4. **Final assembly.** The positive representation count proves prime plus
   prime or semiprime for every even N at or above the exact cutoff.
   The literal original Goldbach.ChenTheorem statement is recovered as a
   corollary. The final audit checks the transitive proof dependencies.

See the [complete numerical proof notes](research/chen-grh/NUMERICAL_CHEN_SUB13.md).
The older H<13.37, H<14, H<29, and standard-only routes remain available. The original
0.67 counting theorem keeps its larger cutoff.

## Full Dirichlet GRH and the certified prefix window

The sole additional axiom, for all Dirichlet characters and all heights, is

$
L(\rho,\chi)=0,\quad0<\Re\rho<1
\quad\Longrightarrow\quad\Re\rho=\tfrac12.
$

The former modulus-one Platt input through height 10^8 follows as a theorem. The Dirichlet seven-eighths input is
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

The complete numerical lower and triple estimates are assembled in the
[H<13 Chen theorem](research/chen-grh/NUMERICAL_CHEN_SUB13.md). Its final audit
and literal recovery of the original implicit statement are checked.

## Verification and scope

The checked upgrade uses Lean 4.34.1 and Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
The [current proof and audit commands](research/chen-grh/NUMERICAL_CHEN_SUB13.md#verification-and-reproduction)
record the completed H<13 Chen proof. See the
[final audit report](research/chen-grh/FINAL_GRHSub13_CHEN_AUDIT.json).
The earlier H<14 and Platt-only reports are historical snapshots.
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
node --expose-gc OpenAI/tools/build-source.mjs AuditGRHSub13Chen
```

For the reproducible hash report, follow the
[GRH audit commands](research/chen-grh/NUMERICAL_CHEN_SUB13.md#verification-and-reproduction),
which set the build tag and serial memory settings before running the final
source/object audit. The report records a completed local check; it does not
replace kernel checking on a fresh source checkout.

Standard-only routes reject custom axioms, placeholders, unsafe proof
dependencies, and native compiler trust. The conditional H<29 audit permits
only the full Dirichlet GRH input. Historical studies, unfinished experiments,
and untrusted numerical scans are not silently promoted to theorem inputs.

## References, provenance, and acknowledgments

- [Alpöge/Claude GRH statement](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/main/src/Statements.lean),
  used as a single axiom instead of importing the large proof;
  [independent verification record](https://math.mit.edu/~drew/grh/).

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
