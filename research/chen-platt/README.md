# Platt modulus-one reciprocal-prefix development

Work in progress. The temporary prefix-window axiom is **still present** in
BJSH30ConditionalProducts.lean. No completed replacement theorem is claimed.
No Platt axiom has been installed yet: analytic estimates currently take its
modulus-one statement as an explicit hypothesis. The final aim is to replace
the old temporary axiom by that sole local Platt axiom and keep cutoff
3^(10^13), H approximately30.027654.

## Checked components

The pinned calr3 analytic closure (70 local modules) compiles on Lean4.34.1:
PsiRanges1e8 and PsiPlateau1e8 use only the modulus-one finite-RH hypothesis
through height100,000,000. The theta conversion is checked in PlattThetaInputs.
No full Dirichlet GRH or binary-Goldbach input is assumed by those bounds.

PlattPrefixBridge proves the direct theta Abel transfer and cancellation of
the canonical Mertens constant in relative reciprocal sums. PlattFarAnchor
proves error at most1e-8 at3^512 from the existing proved theta estimate.
PlattKernelBounds, PlattPlateauKernels, and PlattPlateauNorm give checked
square-root and plateau integrals, including the finite endpoint differences.
PlattLogBounds supplies the elementary logarithm inequalities needed for
the numerical allocations. PlattWindowBudget checks the scalar allocation
59/1e6 + 1/20000 <=1/9000. Its analytic producers still need assembly.

PlattCountSoundness and PlattReciprocalBlocks connect packed sieve counts to
the actual complete reciprocal-prime sum. PlattSegmentArithmetic proves
the integer rounding and segment summation bridge. PlattSegmentPilot gives
a fully kernel-checked reciprocal-sum bound on[4000000,4004096]. The integer
checker is isolated in an Init-only core; each data batch can be checked
without loading the analytic library. PlattRelativeGrid controls every real
point of a cell from certified endpoint data.

The six current count benchmarks pass, including wrong-count rejection and
a262144-integer segment near1e10. The larger1048576-integer stress test
exceeded a4GiB kernel limit; its failed source is excluded from this checked
set. Its measurements are not evidence of a theorem.

The checked proof leaves report only propext, Classical.choice, Quot.sound
(the purely integer leaves use fewer). COMPONENT_STATUS.json records checked
source/object pairs. DEVELOPMENT_AUDIT.json is a static/provenance scan,
**not** a final Chen axiom audit.

## Remaining obligations

The full scan from4e6 through1e10 is untrusted feasibility data. With block
reciprocal enclosures it gives upper error0.00004572215541642777, below the
finite allowance0.00005. There are8,886,581 blocks and239,866 grid points.
The compressed count data and integer log bounds still require complete
kernel replay, a proved logarithm producer, seam and coverage proofs.
The Mertens constant cancels; no numerical enclosure of it is assumed.

The piecewise analytic estimates and exact integral lemmas must also be
assembled into the uniform numerical error bound. Only after both producers
are checked can the temporary axiom be deleted, the single local Platt
axiom activated, and the final H30/old-Chen dependency audits rerun.

## Sources and constraints

Selected sources are from calr3/ternary-goldbach commit
ab016043e852c126492310d8fc44ea7849c381b2. Source-manifest.json records original
hashes, adapted hashes, and compatibility changes. Original Apache2/MIT
licenses and RSBounds provenance are retained. The unrelated eta-plus-square
import was removed from PsiSandwich; its one needed general summability
proof was extracted privately from the same pinned source. Some other
downloaded modules are outside the validated closure.

No native_decide, unproved analytic axiom, or kernel trust bypass was added
to this development. No new external Lake package was added. The existing
prime-power module now uses narrow Mathlib imports; its theorems recompile.
No commit or push was requested or performed in this phase.
