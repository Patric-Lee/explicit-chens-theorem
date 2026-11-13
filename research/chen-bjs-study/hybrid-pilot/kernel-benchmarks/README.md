# Kernel benchmark artifacts

See ../../HYBRID_BRIDGE_STATUS.md
for the mathematical statements, trust boundary, measured results and remaining work.
The first-zero source is pinned IEANTN proof code under its accompanying
Apache-2.0 LICENSE, not a new Lake package. Source URLs and local hashes are
in zero-sources.json. Production Chen proofs do not import the zero benchmark.

From a repository with the established production prerequisites built:

```powershell
./research/chen-bjs-study/check.ps1 -FromModule BJSHybridZeroReindex
./research/chen-bjs-study/hybrid-pilot/kernel-benchmarks/BenchmarkZero.ps1
./research/chen-bjs-study/hybrid-pilot/kernel-benchmarks/BenchmarkPrimes.ps1
```

The first command verifies the bridge and certificate adapters. The next two
reproduce small zero-box and reciprocal-prime certificate benchmarks. Build
products and fresh timings go under .lake/build. They add no dependencies.

The recorded full-prefix-1000 attempt was stopped at about 210 seconds after
reaching 7.43 GB peak memory. Its source is preserved, but it is excluded from
the default benchmark. The successful block [900,1001) does not prove that a
large-range segmented sieve has been implemented or certified.

The zero proof establishes one zero between 14.13 and 14.14. These sources do
not certify the pilot's 500,000 narrow boxes, a complete zero count, or finite RH.

