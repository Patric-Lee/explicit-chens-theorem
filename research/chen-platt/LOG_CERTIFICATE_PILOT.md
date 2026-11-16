# Kernel-checked logarithm pilot

At the actual grid point x=9999935488, PlattLogPilot proves

$$
\frac{882879269665140}{2^{48}}\le\log\log x\le
\frac{882879269665353}{2^{48}}.
$$

The interval width is 213/2^48, approximately7.57e-13. The checker normalizes
logarithm arguments by powers of two, uses16 artanh-series terms, and covers
all directed integer rounding plus the geometric remainder. PlattLogSoundness
proves generic soundness. PlattLogRowSoundness makes the self-contained row
check usable by generated chunks. No Platt hypothesis is needed for logs.

## Measured timings

Lean4.34.1, one thread,4GiB memory cap. Whole-file times include startup and
imports; profiler times below concern the certificate proof.

| Work | Whole file | Profiled proof |
| --- | ---: | ---: |
| One point, arithmetic | 1.332s | 0.011458s |
| 32 actual grid points, arithmetic | 1.923s | 0.132933s |

The32-point batch averages approximately4.15ms per
point of proof work. The real analytic pilot file took
15.343s including Mathlib imports and glue.
The reusable soundness proof took20.393s
to build once. These are small benchmarks, not full-grid timing guarantees.

The integer proof leaves have no axioms. The generic soundness and actual
real-logarithm pilot print only propext, Classical.choice, and Quot.sound.
No native_decide, new dependency, or unproved axiom was introduced.

## Remaining work

The entire239866-point grid is not certified. Regenerate the outward log
bounds with the new uniform33-unit tail and replay all rows. Counts and
reciprocal sums also need their full replay and global grid/seam assembly.
The temporary prefix axiom is still present in the H30 route. Full H30
dependency/axiom audits are deferred to final assembly; chunks only require
kernel checks and source/object/hash receipts.

See MANUAL_CERTIFICATES.md for bounded manual runs. LOG_CERTIFICATE_PILOT.json
records the numeric timing/scope data.
