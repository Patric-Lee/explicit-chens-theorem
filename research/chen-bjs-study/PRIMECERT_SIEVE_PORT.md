# PrimeCert-derived sieve and reciprocal-prime certificates

The minimal port, its connection to the actual reciprocal-prime sums, and
bounded benchmarks are complete. Kernel-checked concrete prefixes are now
available through 100,000. This does not certify the 2e10 pilot grid or change
the complete Chen cutoff; H < 30 remains open.

## Mathematical interface

The port proves that the wheel bitset decides Mathlib's Nat.Prime, including
completeness. The prime flags handle 2 and 3 separately. For scale S > 0,
let

\[
Q=\sum_{p\le n}\left\lfloor S/p\right\rfloor,\qquad C=\#\{p\le n:p\text{ prime}\}.
\]

A checked bitset and a checked weighted accumulator yield the actual bound

\[
\frac Q S\le\sum_{p\le n}\frac1p\le\frac{Q+C}{S}.
\]

The prefix is the existing AnalyticNumberTheory.Mertens.primeReciprocalSum.
The interval adapter gives the corresponding bound for the existing
blockPrimes start (start+len). No new definition of primality or replacement
prime sum is used.

The computation packs the integer sum and count as Q*B+C with B=2^64.
`packedRange_eq`, `fixedSieveRange_count_le`, and
`fixedSieveRange_of_packed` prove decoding, with explicit bounds on length
and count preventing an aliased count. Nat arithmetic is unbounded, so there
is no unchecked machine-word overflow. `packedRange_join` combines checked
summaries through an explicit length equality, avoiding accidental evaluation
of a long prefix during elaboration. Every batch equation is kernel-checked;
the Node generators are untrusted producers of literals.

Public interfaces in ChenEffective.HybridProduct.BitSieve:

- `isSieve_of_sieveK_eq`: checked sieve equation to primality specification.
- `fixedSievePrefix_eq` / `fixedSieveBlock_eq`: equality with the existing
  fixed-point prefix and interval statistics.
- `reciprocal_prefix_of_packed_certificate` and
  `reciprocal_block_of_packed_certificate`: actual real reciprocal-sum bounds.

## Concrete certificates and measured checks

All use S=2^48=281474976710656.

| Endpoint | Q | Count C | Weighted certificate check | Observed peak Lean working set |
| --- | ---: | ---: | ---: | ---: |
| 1,000 | 618704552604687 | 168 | 14.370 s | 1.831 GB |
| 10,000 | 698919240818128 | 1,229 | 16.868 s | 2.115 GB |
| 100,000, serial elaboration | 761466423588538 | 9,592 | 50.967 s | 1.963 GB |

Weighted checks reuse an already checked bitset. The 100,000 bitset check
itself took another 14.506 s with an observed peak of 1.801 GB, giving about
65.473 s for those two stages. Wall times include process startup, imports,
elaboration, kernel checking and output. They exclude the prerequisite
library builds. GB denotes decimal bytes; the raw JSON records byte counts.
The final weighted checks use two Lean threads; the 100,000 comparison also
sets Elab.async=false, which changes scheduling only, not proof checking.

A second successful 100,000 proof uses 13 modules of at most 8,192 integers,
followed by summary assembly: 229.990 s total after the bitset check, with a
maximum observed peak of 2.137 GB. This provides a process-isolated fallback
when a larger single proof file exceeds memory limits.

The initial pair accumulator and asynchronous monolithic 100,000 attempt
exceeded a 4 GiB budget. A previous 10,000 assembly also hit a 180-second cap.
The corrections were reduced imports, scalar packing, explicit summary joins,
and controlled elaboration scheduling. Historical measurements are retained;
their source hashes distinguish them from the final verified sources.

Two deliberately corrupted controls are refused because their checked
propositions are false: a flipped sieve bit and an incremented packed sum.
Import failures or stuck elaboration do not count as successful rejection.

## Audits and provenance

`AuditBJSHybridSieve` traverses 10,010 constants for the general sieve and
sum/block adapters. `AuditBJSHybridSieveBench` traverses 16,730 constants for
the concrete prefixes, the sharded and serial 100,000 routes, and the interval
[900,1001). It requires the actual sieve equation, sieve correctness theorem,
summary composition, decoding, fixed-point rounding proof and canonical prime
sum in the dependency closure. Both reject unsafe constants and unlisted
axioms. Concrete results use exactly propext, Classical.choice and Quot.sound;
they do not need the Dirichlet axiom.

The existing analytic-bridge audit also passed after the import reduction:
69,681 constants, exactly the existing Dirichlet axiom plus standard axioms.

Only PrimeCert's sieve, its correctness proof and the necessary bitwise/mod-6
helpers were adapted, at commit d84a15cacfdc45ae1e96e56dd58158f871787870.
See hybrid-pilot/primecert-port/NOTICE.md, the preserved original license,
source-manifest.json and benchmark-results.json. No PrimeCert package, Hex,
OpenAI module, new external dependency or toolchain upgrade was introduced.
The source version's 32 mask rounds and endpoint cap 12884901888 remain.

## Reproduction

After the existing production prerequisites are built:

```powershell
./research/chen-bjs-study/check.ps1 -FromModule BJSHybridPrimeCertificate
./research/chen-bjs-study/hybrid-pilot/primecert-port/Benchmark.ps1
```

The default benchmark runs the already demonstrated small prefixes and the
100,000 serial route with a 180-second / 4-GiB per-process budget. Fresh
artifacts and measurements go under .lake/build/hybrid-primecert-benchmark.
The library build also checks the general proof audit. The rejection controls
can then be replayed independently:

```powershell
./research/chen-bjs-study/hybrid-pilot/primecert-port/Benchmark.ps1 -Modules BJSHybridSieveBadData1000,BJSHybridSieveBadPacked1000 -ExpectedFailures BJSHybridSieveBadData1000,BJSHybridSieveBadPacked1000
```

To regenerate the untrusted literals, from the same folder:

```powershell
node GenerateHybridSieveBench.mjs 1000 10000 100000
node GenerateHybridSieveShards.mjs 100000
```

The sharded route is optional and is needed to reproduce the full concrete
audit, which imports both successful 100,000 routes:

```powershell
$plan = Get-Content ./research/chen-bjs-study/hybrid-pilot/primecert-port/benchmarks/sieve-shards-100000.json -Raw | ConvertFrom-Json
./research/chen-bjs-study/hybrid-pilot/primecert-port/Benchmark.ps1 -Modules $plan.modules
./research/chen-bjs-study/hybrid-pilot/primecert-port/Benchmark.ps1 -Modules AuditBJSHybridSieveBench
```

## Scaling boundary

This is a prefix bitset sieve with a block-sum adapter, not yet a high-offset
segmented sieve. Reading an interval currently still requires the certified
prefix bitset covering that interval. The next scaling work is a verified
high-offset segment specification/marker, bounded proof modules and larger
weighted-batch calibration. The 2e10 endpoint also exceeds the preserved
32-round cap. The full finite prime grid, logarithm/B1 certificates, zero
certificates and remaining Chen lower-count assembly are not discharged by
these 100,000-prefix benchmarks.
