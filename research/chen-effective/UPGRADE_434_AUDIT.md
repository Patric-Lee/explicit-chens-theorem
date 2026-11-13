# Lean 4.34.1 / proved Dirichlet integration audit

Verified at 2026-11-13T07:36:32.097Z.

- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Vendored OpenAI revision: `4eaee87548250b2682affda7d05d947c05554bae`.
- 1084 modules in the final Chen closure; 1086 in the combined integration check.
- No new external Lake package names.

| Result | Additional axioms beyond Lean's standard three |
| --- | --- |
| Dirichlet seven-eighths theorem | None |
| Tight-budget Chen theorem, cutoff 3^(3^134), H approximately 147.308095 | None |
| Conditional numerical Chen theorem, cutoff 3^(10^13), H approximately 30.027654 | temporary_reciprocal_prefix_window |

Both new recovery theorems have exactly the type of the original `Goldbach.chen_theorem`. The detailed transitive audits reject unsafe proof dependencies, unapproved axioms, proof placeholders, and native/compiler-trust proof dependencies. They require the actual proved OpenAI Dirichlet theorem in the final dependency chain.

The source scan checked 3513 Lean files and found only the authorized temporary reciprocal-prime window axiom. All 2924 pinned OAI source hashes and 2939 source-mapped OAI/Rellich proof bodies were verified. Grouping annotations are recorded in the manifest.

Large cutoff representations use kernel-checked equality certificates where necessary to avoid forcing impossible numeral evaluation. Their exact numerical equations are proved; no numerical assumption was added for those representations.

The validation scope is the active Chen development and its original-statement compatibility bridge. The separately retained upstream Li-Liu/Wu development has its own build scope.

## Reproduce

After installing the pinned toolchain and obtaining the pinned Mathlib cache:

```text
node OpenAI/tools/audit-sources.mjs --dirichlet-proved
node OpenAI/tools/verify-sources.mjs
node OpenAI/tools/build-source.mjs OAI.AuditChenIntegration
```

Set CHEN_BUILD_JOBS=1 for lower peak RAM. All proof terms are checked by Lean; no native_decide or kernel-checking bypass is used. The temporary reciprocal-prime certificate window remains unproved.

## Combined audit output

```text
Standard-only proof: ChenEffective.dirichlet_seven_eighths; axioms [propext, Classical.choice, Quot.sound]
Standard-only proof: ChenEffective.TightBudget.chen; axioms [propext, Classical.choice, Quot.sound]
Standard-only proof: ChenEffective.TightBudget.original_chen; axioms [propext, Classical.choice, Quot.sound]
Standard-only proof: ChenEffective.bjsStudy_chen; axioms [propext, Classical.choice, Quot.sound]
Standard-only proof: ChenEffective.joint_chen_81; axioms [propext, Classical.choice, Quot.sound]
Standard-only proof: ChenEffective.expanded_chen; axioms [propext, Classical.choice, Quot.sound]
Conditional proof: ChenEffective.H30Conditional.chen; axioms [propext,
 Classical.choice,
 Quot.sound,
 ChenEffective.H30Conditional.temporary_reciprocal_prefix_window]
Conditional proof: ChenEffective.H30Conditional.original_chen; axioms [propext,
 Classical.choice,
 Quot.sound,
 ChenEffective.H30Conditional.temporary_reciprocal_prefix_window]
Recovery dependency audit: ChenEffective.TightBudget.original_chen; 133656 constants; numerical producer and actual Dirichlet proof present.
Recovery dependency audit: ChenEffective.H30Conditional.original_chen; 133625 constants; numerical producer and actual Dirichlet proof present.
Chen integration audit passed: Dirichlet is proved; both literal old Chen statements recovered.
'ChenEffective.TightBudget.chen' depends on axioms: [propext, Classical.choice, Quot.sound]
'ChenEffective.TightBudget.original_chen' depends on axioms: [propext, Classical.choice, Quot.sound]
'ChenEffective.H30Conditional.chen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ChenEffective.H30Conditional.temporary_reciprocal_prefix_window]
'ChenEffective.H30Conditional.original_chen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ChenEffective.H30Conditional.temporary_reciprocal_prefix_window]
```

The companion JSON retains source/object hashes, version configuration hash, and the individual audit outputs.
