# Vendored OpenAI Dirichlet seven-eighths proof

**The complete OpenAI proof and adapter have compiled and passed their transitive audit. The local Dirichlet axiom is removed. The upgraded final Chen and combined integration audits have also passed.**

The user authorized importing this proof on 2026-11-12. This folder contains
the actual solution, not the Comparator challenge with a placeholder.
The 2,924-module OAI dependency closure is pinned to openai/math commit
`4eaee87548250b2682affda7d05d947c05554bae` under Apache-2.0 (see LICENSE).
The 15-file Rellich compactness closure is pinned to
`70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23`; its license is retained in
Rellich-LICENSE. The existing local PrimeNumberTheoremAnd sources supply the
other non-Mathlib import. No additional external Lake package is required.

Upstream requires Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The repository pins have now been upgraded to these versions; old build
artifacts are retained separately. All 74 generated units, the existing Wiener/PNT dependency, the adapter,
and its audit have compiled. The audit traversed 122,474 constants and
reported only `propext`, `Classical.choice`, and `Quot.sound`.

`source-manifest.json` records the original OAI source hashes and imports.
`rellich-source-manifest.json` records the original third-party closure.
The upstream Rellich compatibility patch is retained as `rellich-lean4341.patch`.

`OAI.ChenDirichlet` is the active adapter. Its declaration has exactly the
name and type of `ChenEffective.dirichlet_seven_eighths` but is a theorem
derived from the actual OpenAI result. `OAI.AuditChenDirichlet` is the required
transitive audit: it rejects nonstandard axioms, placeholders, unsafe proof
dependencies and native compiler trust.

The active `ExplicitSiegel` module imports the proved adapter. Its former
axiom declaration is deleted, and the final Chen audit allowlists have been
tightened. The full upgraded Chen dependency closure and final audits passed. Both
numerical recovery theorems have exactly the original Chen statement type,
and their proof dependencies include the actual OpenAI theorem. See the
[final audit report](../research/chen-effective/UPGRADE_434_AUDIT.md).

The temporary reciprocal-prime window is a separate remaining input. Proving
the Dirichlet theorem does not certify the finite prime or zero tables.

## Grouped compilation

The original 2,924 OAI files and 15 Rellich files are retained unchanged apart
from the recorded upstream Rellich compatibility patch. To reduce repeated
import costs, their proof bodies are compiled in 74 source-mapped units under
`grouped/`. Each original file has its own section scope. The manifest records local alias
annotations and explicit namespace qualifications needed when sibling modules
are combined; all other proof text is retained. No proof body is
replaced by a trusted computation. Lean checks all generated proof terms.
`grouped-manifest.json` records source hashes, unit hashes, and imports.
The public adapter uses thin wrapper modules under `wrappers/`.

Regenerate with `node OpenAI/tools/generate-groups.mjs 40`.
After obtaining the pinned Mathlib cache, the bounded build is
`node OpenAI/tools/build-source.mjs OAI.AuditChenDirichlet`.
It uses two workers by default, one Lean thread per worker, a 6-GiB
Lean memory limit for grouped OpenAI units, and 4 GiB for ordinary modules.
The finite BJS table check and transitive audit fixtures have an 8-GiB limit
and run alone. These are caps, not measured minimum RAM requirements. Set CHEN_BUILD_JOBS=1 for a serial run.
Successful module objects and source/dependency hashes are recorded under
`.lake/build-434/source-build-logs` for resumable checking.

The ordinary Lake target `lake build +OAI.AuditChenDirichlet:olean` is
also available. The bounded runner makes memory use more predictable.
