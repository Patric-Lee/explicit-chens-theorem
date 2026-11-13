# Checked bitset sieve and reciprocal-prime benchmarks

See [the proof interfaces, results and reproduction instructions](../../PRIMECERT_SIEVE_PORT.md).

`NOTICE.md` and `LICENSE.PrimeCert` preserve upstream provenance and licensing.
`source-manifest.json` hashes the verified local sources. `benchmark-results.json`
records actual successful checks, historical resource-limit stops and corruption
controls; a measurement's source hash identifies its exact version.

The default `Benchmark.ps1` run checks the demonstrated small prefixes and the
100,000 serial route. It uses two Lean threads, a 180-second per-process limit,
and a 4-GiB per-process memory limit. The optional 13-module route provides a
second checked 100,000 certificate with bounded process memory. Build products
are written under `.lake/build/hybrid-primecert-benchmark`.

The negative-control sources deliberately assert false numerical propositions.
Run them only with the listed `-ExpectedFailures` arguments; the driver requires
an explicit false-proposition diagnostic rather than accepting arbitrary errors.

No new package dependency is installed. These examples certify actual
reciprocal-prime sums through 100,000; they do not certify the full 2e10 grid.
