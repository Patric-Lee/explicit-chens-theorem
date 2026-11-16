# Checked assembly pilot after completed counting

The counting campaign is complete: all 76,265 current receipt/source/object
triples, configuration and dependency hashes, numerical statement templates,
and chunk-plan seams were verified. There are no missing or unresolved failed
chunks. The read-only verification took 258 seconds. This is a component
verification, not a fresh replay of all computations or the final Chen audit.

The new single-pass `checkPrefixCuts` reuses the existing packed prime counts.
`PlattAssemblySoundness` proves its relation to the actual reciprocal-prime
prefix sums, cumulative interval addition, the meaning of integer grid budgets,
and all-real cell-chain coverage. `PlattAssemblyPilot.VerifiedPilot` closes
concrete genuine prime-sum bounds for the first eight count chunks and across
the old count-section boundary at chunks 9999/10000. Its first grid batch has
proved all-real coverage. The printed axiom reports contain only standard Lean
axioms. No new external package or local axiom is introduced; no `native_decide`
is used.

## Measurements

| Pilot | Whole-file Lean time | Sampled peak Lean RAM |
|---|---:|---:|
| Dense first count chunk: 1,021 prefix checkpoints | 4.13 s | not sampled |
| Next count chunk: 396 checkpoints | 2.24 s | not sampled |
| Later count chunk: 4 checkpoints | 1.16 s | not sampled |
| 256 grid-budget/cell-seam checks, one worker | 1.75–1.81 s | not sampled |
| Cumulative proof over first 8 chunks | 7.15 s | 612 MiB |
| Cumulative proof over first 32 chunks | 23.17 s | 1,497 MiB |
| Cumulative proof over 32 later chunks | 2.76 s | 359 MiB |
| Cumulative proof across an old section seam, 16 chunks | 1.96 s | 298 MiB |

Eight concurrent grid workers checked eight disjoint batches of 256 cells
(2,048 cells total) in **9.76 seconds**, including the coordinator startup/cache
checks. All eight native Lean processes were observed concurrently. Their
aggregate sampled working-set peak was **2,309 MiB**, with **4,397 MiB** minimum
free physical memory. Working-set sums can include shared pages. These are
small-pilot measurements, not a forecast for the entire assembly.

The first repeated-lookup prefix implementation approached the 2 GiB cap and
was stopped; the single-pass replacement passes. An unsealed dense 256-chunk
cumulative batch exceeded 2 GiB. The kernel-defined opaque-packet version
passed at the same cap in about 103 seconds. Packet opacity introduces no axiom:
each packet has a checked initializer containing both original certificates.
Large dense batches are not the recommended scheduling unit.

## Numerical feasibility and remaining work

An independent integer feasibility scan over every one of the 239,865 grid
cells, using the certified log-row values and the checker-compatible floor+1
upper rounding, gave the enclosure

\[
[-0.000003219692808,\;0.000045905813068]
\subset[-1/20000,1/20000].
\]

This scan is JavaScript evidence; the full all-grid statement is not yet a Lean
theorem. It shows that simpler independent cumulative intervals fit the budget,
so correlated suffix-error cancellation is unnecessary for the current route.

The remaining production work is a resumable assembler for all cumulative and
interior-checkpoint certificates, a bounded aggregation tree, all grid batches,
and the final reference-bound/analytic-window integration. Global coverage must
join every section seam and include the overall endpoints. The pilot proves the
generic coverage theorem and representative seams, not this full join.

Use eight workers for the small arithmetic grid stage. Cumulative scheduling
should use smaller early batches and a memory-aware worker limit; eight early
32-chunk jobs could exceed this machine's RAM. No large campaign was started.
The production endpoint is still 1e10 and H30 still retains the temporary prefix
axiom pending the complete replacement and final audit.

See `ASSEMBLY_PILOT_REPORT.json` for the current source/object/dependency hashes
and measured resource data. `tools/VerifyCountCampaign.mjs REPO [REPORT.json]`
repeats the read-only count-campaign verification.
