# Platt-only explicit Chen theorem below H = 29

The temporary reciprocal-prefix axiom has been removed. The checked theorem
`ChenEffective.H29Conditional.chen` proves Chen's conclusion for every even
`N ≥ 3^(3*10^12)`, corresponding to H = 28.82368123221. Lean also
proves this cutoff is strictly below exp(exp(29)). The literal original
`Goldbach.ChenTheorem` follows as `original_chen`.

The sole external axiom is `PlattWindow.platt_modulus_one_finite_RH`, declared
in [PlattAssumption.lean](PlattAssumption.lean): every nontrivial zeta zero
with imaginary part of absolute value at most 100,000,000 has real part 1/2.
It has exactly the `TernaryGoldbach.PlattZetaRH` predicate used by the local
calr3 port. It asserts neither full RH nor Dirichlet GRH. The Dirichlet
seven-eighths theorem is supplied by the existing checked OpenAI proof.

## Finite certificate and analytic tail

Write P(x) for the reciprocal sum over primes up to x and
E(x) = P(x) − log log x − B₁, with the canonical Mertens constant B₁.

[PlattFiniteWindow.lean](PlattFiniteWindow.lean) proves, with only standard
Lean axioms,

\[
|P(x)-P(10^{10})-(\log\log x-\log\log 10^{10})|
\le \frac1{20000}\qquad(4\cdot10^6\le x\le10^{10}).
\]

The finite computation consists of 76,265 sieve/count certificates over
8,886,581 blocks, 937 logarithm chunks, and 239,866 grid points. The completed
assembly has 2,723 prefix, 2,399 totals, and 943 grid batches. All are kernel
checked using `decide +kernel`. No prime-count or logarithm computation is
accepted as an axiom.

`PlattPointPacketSoundness` proves the cumulative prefix carry induction.
`PlattGlobalGridSoundness` matches the actual prime bounds and certified log
rows to each integer cell budget and proves all-real coverage, including
section seams. `PlattGlobalPointCover` assembles 943 bounded point-stream
checks using proved structural inclusions into the global prefix tree.
Each merge accepts repeated seam points but rejects altered bounds.

The ten downstream H≈30 proof modules are checked together in
`BJSH30ConditionalChen.lean` to avoid repeatedly importing the large
certificate closure. Their original proof bodies are retained unchanged in
`../chen-numerical-study/proof-sources/H30Conditional/`, with a source/hash
manifest and thin compatibility import modules. The earlier H≈30 audit checked
body preservation as well as the resulting Lean proof and axiom closure.
`PlattGlobalGridNegativeControls` checks missing-point and mismatched-row
rejection. No numerical sieve is replayed by these proof joins.

Under the Platt hypothesis, [PlattAnalyticWindow.lean](PlattAnalyticWindow.lean)
proves |E(x)| ≤ 59/10⁶ on [10¹⁰, 3⁵¹²]. This includes the reference anchor
and the tail through 3¹²⁰. The exact allocation

\[
\frac{59}{10^6}+\frac1{20000}\le\frac1{9000}
\]

gives the full prefix window in
[PlattCertifiedPrefixWindow.lean](PlattCertifiedPrefixWindow.lean).
The canonical B₁ cancels in the finite comparison. No numerical enclosure of
B₁, unverified zero ordinates, or additional Büthe/Schoenfeld assumption is used.

## Variable budget below H = 29

The new H29 lower proof is generic over a proved prefix window. Its concrete
instance is supplied by the same completed finite certificates and Platt
analytic tail, in BJSH29ConditionalChen. No window hypothesis remains in the
public numerical Chen statement.

The contraction allowance is 1/30000, and both distribution exponent-loss
denominators are 300,000,000. The base mass budget remains 20,000,000 and the
medium mass budget 5,000,000. A slightly larger factor allowance still fits
the original 1/20 lower-count loss and 113/100 medium-count loss.

The upper proof uses the already-proved sharp Mertens product in its actual
Pan normalization, replacing the older large-threshold input in that branch.
It keeps the remainder as 2 C₅/L³ + 38/L until the final Chen budget. Both
the lower and complete upper counts now hold at 3^(3*10^12). The old H≈30
route and its historical audit remain available.

See [the exact H29 statements and proof budget](../chen-numerical-study/NUMERICAL_H29.md).

## Audits and reproduction

[FINAL_CHEN_H29_AUDIT.json](FINAL_CHEN_H29_AUDIT.json) records the final source/object
manifest and transitive audit. The final numerical theorem and its recovery
of old Chen have exactly `propext`, `Classical.choice`, `Quot.sound`, and the
one published Platt input as axioms. The audit rejects placeholders, unsafe
proof dependencies and native compiler trust, and requires the actual lower
and triple counts, proved Dirichlet theorem, finite window and analytic tail.
The independent H≈147 route retains its standard-only audit.

For a fresh Windows checkout, preserve the vendored-source checksum line
endings by cloning with a repository-local Git setting:

```sh
git clone -c core.autocrlf=false https://github.com/Patric-Lee/explicit-chens-theorem.git
```

From a configured checkout, use:

```sh
node --expose-gc OpenAI/tools/build-source.mjs AuditBJSH29Conditional AuditBJSTightBudget OAI.AuditChenIntegration
```

The checked artifacts are reusable. A source-only checkout still needs to
check the finite certificate sources; it does not gain trust from the JSON
receipts or the JavaScript feasibility scans. Existing completed counting,
logarithm and assembly campaigns do not need to be rerun locally.

## Build time and memory

Budget **15+ hours for a first full certificate build and assembly** on hardware
comparable to the development machine, plus time for dependency setup and
final global proof/audit checks. Runtime varies with CPU, storage, available
memory, paging and worker count. This estimate is not a fresh end-to-end
benchmark: the completed counting report records 234,443.952 seconds (about
65.1 hours) of summed Lean process time across workers, which is distinct
from elapsed wall time. Other stages add work.

Observed resource use on Windows:

| Item | Observation or guidance |
| --- | --- |
| Physical RAM on the development machine | About 14 GiB usable |
| Largest serial Lean import/audit process | About 20–22 GiB private committed memory; not resident RAM |
| Recommended physical RAM | 32 GiB for less paging; this is guidance, not a formally measured minimum |
| Smaller machines | A 16 GiB machine needs substantial available swap/pagefile capacity and may be much slower |
| Parallelism | Chunk workers can run concurrently; keep large global joins and final audits serial |

Allow commit headroom beyond the Lean process for the operating system and
other applications. The development build succeeded with paging; do not
interpret its physical RAM size as a no-swap memory bound. Kernel-checked
objects and dependency caches also consume disk space separately from RAM.

For scale, the earlier H≈30 release’s fresh downstream Chen check took about 20.7 minutes,
the focused H≈30 audit 8.7 minutes, and the combined integration audit 16.6
minutes on this machine, with heavy import/paging costs. These are observed
individual runs, not reliable forecasts for other hardware.

A fresh clone contains proof/certificate sources, not this machine's
`.lake/build-434` object cache. It must check those sources. Once checked,
unchanged local artifacts can be reused; there is no need to repeat completed
local campaigns just to rerun an unchanged final theorem. The saved JSON
receipts and untrusted numerical scans do not substitute for Lean checking.

## Sources and constraints

The analytic port is from calr3/ternary-goldbach commit
ab016043e852c126492310d8fc44ea7849c381b2. source-manifest.json records the
selected original files, adaptations, and hashes. Apache-2.0/MIT licenses and
RSBounds provenance are retained. Selected calr3 modulus-one estimates are
used; unrelated downloaded studies remain outside the final proof closure.
The optional lower-endpoint Büthe route remains a separate study.

No `native_decide`, proof placeholder, additional unproved analytic input,
or new external Lake package is used. Lean 4.34.1 and the existing pinned
Mathlib/LeanArchitect dependencies are unchanged.
