# Restartable finite certificate chunks

Run from the repository root in PowerShell. Node and the pinned Lean/Lake
toolchain are needed; no new package is installed. The full local untrusted
scan inputs must be present: block-relative-1e10.grid.json.gz,
block-relative-1e10.counts.bin.gz, and block-relative-1e10.json. The generator
tools/BlockRelativeScan.mjs can recreate the proposals; the proposals themselves
are not proofs. First ensure the checked kernel modules are available locally.

## Commands

If PowerShell cannot find node, use the wrapper from any directory:

~~~powershell
$cert = 'C:\Users\89270\Desktop\Vibe\goldbach-lean\research\chen-platt\tools\CertificateChunks.ps1'
& $cert status --kind logs
& $cert status --kind counts
& $cert run --kind logs --start 1 --chunks 10
~~~

The wrapper finds the existing Codex-bundled Node and Git executables and
supplies their directories to child processes temporarily. It makes no permanent PATH change.
The node commands below require running from the repository root with Node
on PATH. Do not append backslashes to the ends of PowerShell command lines.

Inspect the plans:

~~~powershell
node research/chen-platt/tools/CertificateChunks.mjs status --kind logs
node research/chen-platt/tools/CertificateChunks.mjs status --kind counts
~~~

Run one chunk, or a small range:

~~~powershell
node research/chen-platt/tools/CertificateChunks.mjs run --kind logs --start 1 --chunks 10
node research/chen-platt/tools/CertificateChunks.mjs run --kind counts --start 1 --chunks 10
~~~

Chunk0 of each kind has already passed a smoke test on this machine.
Rerun any range safely: the builder checks hashes and reuses unchanged
checked objects. Stop after a chunk, or interrupt with Ctrl+C and rerun the
same range. A success receipt is written only after a successful Lean build.
The section mode below supports independent concurrent workers. Updated runners
refuse overlapping ranges. Stop commands started with the older runner before
switching; older processes do not participate in the new locks.

## Parallel, resumable sections

The default counting campaign is partitioned into eight fixed sections:

| Section | Global chunk indices (inclusive) |
|---|---|
| 1 | 0–9999 |
| 2 | 10000–19999 |
| 3 | 20000–29999 |
| 4 | 30000–39999 |
| 5 | 40000–49999 |
| 6 | 50000–59999 |
| 7 | 60000–69999 |
| 8 | 70000–76264 |

Each selected section runs one worker, with one Lean thread. Resume one section
and check up to 100 unfinished chunks:

~~~powershell
& $cert run --kind counts --section 3 --chunks 100
~~~

Rerun the same command for the next 100. Already checked chunks with matching
source, object, configuration, grid-input and dependency hashes do not count
toward this limit. Missing or stale receipts are checked again. Omitting
`--chunks` runs the rest of the selected section. Existing chunks from the old
sequential campaign are reused; there is no reset or renumbering.

Select two or four workers from one terminal:

~~~powershell
& $cert run --kind counts --sections '3,7' --chunks 100
& $cert run --kind counts --sections '2,3,4,5' --chunks 100
~~~

Here `--chunks 100` applies separately to each section. These are alternative
examples: do not start both while their selected sections overlap. You can also
run separate `--section` commands in different terminals. The eight sections
are scheduling choices, not a requirement to run eight processes simultaneously.
Start with two workers and increase if memory and responsiveness permit.

Inspect completion globally or for a particular section:

~~~powershell
& $cert status --kind counts
& $cert status --kind counts --section 3
~~~

Status reports historical receipts; resume validates their hashes. `--start`,
if supplied with `--section`, is an absolute global chunk index inside that
section. Usually omit it to resume automatically. Without a section, the legacy
`--start`/`--chunks` behavior remains unchanged and takes an exclusive campaign
lock.

### Failed chunks and gaps

A chunk failure is recorded under
`.lake/build-434/manual-certificates/<variant>/failures/Cxxxxxx.json` with the
chunk index, time, stage, error, attempt count and build-log paths. The worker
then continues with the next chunk. Failed chunks count toward `--chunks`,
which limits attempts rather than successful results. A run with failures
returns a nonzero exit code after finishing its requested attempts and lists
the failures in its final summary. Other selected sections can still finish.

Resume with the same section command, normally omitting `--start`. It scans
from the section's beginning, reuses matching successes, and retries gaps before
moving on. Later successes do not advance a cursor past an earlier failure.
Successful retries mark the failure record `RESOLVED`, retaining its history.
Status lists unresolved failures; `nextUnrecordedChunk` and `nextPendingChunk`
both identify the earliest missing receipt or explicitly failed chunk, rather
than the highest processed index plus one. Explicit failures are not counted as
successful even if an older historical receipt exists. Status remains a quick
receipt report, not the final source/dependency/coverage audit.

Global input-validation and lock errors still stop a worker. If a failure record
itself cannot be saved, the worker also stops rather than silently losing it.
After changing the runner, restart existing commands to load the new behavior.

Each section writes its own build ledger/status, using atomic JSON replacement.
Locks prevent overlapping work, including the legacy mode. An interrupted
driver's build child keeps its range locked until it exits. Dead process locks
are reclaimed on the next run. Avoid changing checker sources during a campaign:
section workers require cached shared dependencies and refuse to rebuild them
concurrently. If that check fails, stop all workers, build the named dependency
once, then resume. No additional mathematical assumptions are introduced.

On Windows, ledger, receipt and lock JSON replacements retry transient `EPERM`,
`EACCES` and `EBUSY` errors for up to ten seconds. The destination is never
deleted as a fallback. If replacement still fails, the pending JSON is retained
and the error names its path. Stop and resume the affected section; an existing
matching checked object can be reused even if its receipt was not yet saved.

Use prepare instead of run to generate sources without compiling. Merely
preparing a chunk does not certify it. Use --memory-mb 4096 to set the Lean
cap (the default is4GiB). Each Lean process uses one thread. The default
count chunks span at most131072 integers; log chunks contain256 grid rows.
These defaults produce937 log chunks and76265 count chunks.

The first checked256-row log chunk took4.33s of Lean whole-file time; the
first checked count-plus-arithmetic chunk took2.54s. These small low-range
measurements do not predict the full campaign or high-end resource cost.

## What each chunk establishes

Log chunks contain self-contained LogRow certificates. checkRow verifies
normalization ranges, log bounds, and outer-log bounds with integer arithmetic.
PlattLogRowSoundness.checkedRows_sound transfers each checked row to the
true real log-log enclosure. This newly generated data uses the proved
outward33-unit geometric remainder; it does not silently trust the original
JavaScript log bounds.

Count chunks check the minimal sieve's packed prime counts, then separately
check segmentFixed reciprocal-sum rounding for that packed data. The existing
PlattSegmentArithmetic.segment_reciprocal_certificate supplies the real
prime-sum meaning. The count checksum is verified before generation.
The upper rounding is floor+1 per block, matching the proved segment kernel;
it can be slightly wider than the original feasibility scan's ceiling.

Source files go under research/chen-platt/PlattCertificates/. Successful
source/object/input/hash receipts go under
.lake/build-434/manual-certificates/. The ordinary source-build ledgers
retain dependency hashes and elapsed times. Status counts historical receipts;
run is the command that checks their compatibility with current sources.

## Audit and final proof

Every chunk MUST pass the ordinary Lean kernel. No full Chen dependency/axiom
audit is run for each chunk. Run the full audit after the H30 route has been
assembled, and rerun it if the final theorem or its dependencies change.

These runners cover count/segment-arithmetic and log certificates only.
They do not yet prove the global reciprocal-prefix inequalities or grid
coverage. Their final integration must join all count groups and grid cells,
use the certified outward rounding, prove coverage/seams, and replace the
temporary prefix axiom before the final H30 audit. A collection of receipts
alone is not the completed H30 theorem.

## Reuse when lowering H

Changing the final H does not invalidate these facts about primes and logs.
Reuse unchanged ranges, grid points, and checker modules. A smaller pre-sieve
start needs additional lower-range certificates. A tighter tolerance may need
new grid points or finer count blocks; existing coarser count blocks cannot
be subdivided without further information. Changing proof/checker definitions
can invalidate dependency caches and require kernel replay, so keep the core
stable during the campaign.
