# Resumable finite-window assembly jobs

The prime-counting and logarithm campaigns are complete. These jobs reuse those
certificates; they do not launch a new prime sieve. All new leaf facts are checked
by the ordinary Lean kernel, with no new axioms, dependencies or native_decide.

## Run on the current machine

The preparation files have already been generated and tested on this checkout.
Paste the following into PowerShell. Each command waits for its selected sections
to finish before the next command starts:

```powershell
$assembly = 'C:\Users\89270\Desktop\Vibe\goldbach-lean\research\chen-platt\tools\AssemblyChunks.ps1'
$sections = '1,2,3,4,5,6,7,8'

& $assembly run --kind prefix --sections $sections --jobs 4
& $assembly run --kind totals --sections $sections --jobs 4
& $assembly run --kind grid --sections $sections --jobs 8
```

The wrapper finds Node and Git as the counting wrapper does. It works from any
current directory and makes no permanent PATH change. The worker limit is per
command: run one stage at a time rather than launching all three simultaneously.

For bounded runs, add `--chunks 100` to any run command. This means at most 100
unfinished **assembly-batch attempts per selected section**, not 100 of the old
counting chunks. Repeat the same command to proceed. Completed matching leaves
are skipped after hash checks. A particular section can be selected with
`--section 3`; a subset with `--sections '3,7'`. `--jobs` limits simultaneously
active sections, so all eight sections may be selected with only four workers.

Check progress:

```powershell
& $assembly status --kind prefix
& $assembly status --kind totals
& $assembly status --kind grid
```

Each section reports its total batches, recorded successes, earliest pending
batch and unresolved failures. Status is a receipt report; run validates current
sources, compiled objects, configuration and dependency hashes. A chunk failure
is recorded and later batches continue. Failures count toward `--chunks`; a run
with failures returns a nonzero exit code. Repeating the command fills gaps
without recompiling valid later successes. If the failure record itself cannot
be written, the worker stops. Overlapping workers for the same stage/section are
refused, and atomic JSON writes retry temporary Windows file-sharing errors.

Ctrl+C and the same resume command can be used. An interrupted native child may
need time to exit before its range lock is released. Do not change core checker
sources or proposal files while workers are running.

## Stages and batch sizes

| Stage | Checked facts | Batch sizing |
|---|---|---|
| `prefix` | Within-chunk reciprocal checkpoints, coordinates and arithmetic links to proposed global point bounds | First 128 count chunks: 4 per batch; rest of section 1: 16; other sections: 32 |
| `totals` | Existing sieve/arithmetic facts packaged into certified increment lists, exact seams and summed bounds | First 128 count chunks: 8 per batch; otherwise 32 |
| `grid` | Integer error budgets, all internal cell seams, and exact links to existing log-row data | 256 cells per batch, with shorter final batches |

Prefix and totals sections keep the original count ranges: section 1 covers count
indices 0–9999, section 2 covers 10000–19999, and section 8 ends at 76264. Grid
sections instead cover consecutive groups of 30,000 cells, with the common
boundary point retained at each seam. The plans have no gaps or overlaps in
their covered cells/count indices. The last batch of a region can be shorter.

The final plan has 2,723 prefix batches, 2,399 totals batches, and 943 grid
batches. Default worker limits are four for prefix/totals and eight for grid.
Each Lean child uses one thread and a 2 GiB cap; `--memory-mb` changes the cap,
not a reserved RAM allocation. Early inputs are denser and are intentionally
split into smaller batches. Existing pilot timings are in ASSEMBLY_PILOT.md;
they are not forecasts for the whole campaign.

Generated Lean modules live under `research/chen-platt/PlattAssembly/`.
Successful receipts and failure records live under
`.lake/build-434/assembly-certificates/<Stage>/S<section>/`. Worker ledgers and
logs are separate from the original counting ledgers. The original 76,265 count
certificates and 937 log certificates are preserved.

## Preparation and final integration

Only if preparation is missing, or on a separately prepared checkout, run:

```powershell
& $assembly prepare
```

Preparation reads the completed receipts and scan inputs, derives the shared
proposal data, and verifies input hashes and numerical feasibility. It is not a
Lean proof. Stop all assembly workers before preparing again. Normally prepare
once, then resume with run; do not regenerate the data for every batch.

These three stages produce certified leaves, not the final Chen theorem. After
all three are complete, the remaining proof work is the bounded global
cumulative tree and incoming offsets, full cross-section grid/point/log joins,
the analytic-window connection, replacement of the temporary prefix axiom by
the Platt-based theorem, and the final Chen axiom/coverage audit. A collection of
success receipts alone does not prove that the complete window has been joined.
