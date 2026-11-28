# Finite-band experiment towards H = 10

The experiment partitions the gap between exp(exp(10)) and the saved
cutoff 3^145000. It does **not** establish Chen's theorem on this gap.
The checked Chen cutoff remains H approximately 11.97854.

The [generator](tools/ExperimentH10Bands.mjs) and
[complete numerical report](H10_FINITE_BAND_EXPERIMENT.json) record all
199 bands, parameter proposals, margins and unresolved analytic inputs.
The [Lean-check record](H10_BAND_COMPONENT_CHECK.json) binds the new
checked source/object pairs and their printed axiom closures. It is a
component record, not a final Chen audit.

## Coverage and pasting

The exact integer endpoints start at 22026 and end at 159500. Each next
endpoint is ceil(101 a/100), capped at 159500. Bands use the half-open
convention [a,b). Two elementary comparisons are proved in Lean:

$$
22026\le e^{10},\qquad \log(3^{145000})\le159500.
$$

Thus any natural N >= exp(exp(10)) either lies in a band or already
satisfies N >= 3^145000. The generated
[GRHH10BandCover.lean](GRHH10BandCover.lean) proves exact coverage, including
every boundary, and `paste_saved_cutoff` proves the generic gluing step.
It takes both the interior proofs and the saved theorem as explicit
arguments. It does not fabricate an interior proof from numerical fits.

## Analytic components proved in this experiment

[GRHH10PrimeIntervals.lean](GRHH10PrimeIntervals.lean) retains the existing
Mertens power error and connects it to the actual floored prime intervals.
For L = log N >= 2400 and 1/10 <= a <= b, it proves

$$
\left|\sum_{N^a<p\le N^b}\frac1p-\log(b/a)\right|
\le\eta_*(L),\qquad
\eta_*(L)=\left(\frac{255}{L}+\frac{2400}{L^2}\right)e^{-L/160}.
$$

This uses two already-proved Mertens prefix errors. Its constant is slightly
larger than the direct partial-summation proposal in the preceding study;
the experiment uses this proved, conservative version throughout.
At the H10 lower endpoint it is about 1.90e-62, still far smaller than
1/L^2. Floor endpoints and the strict/non-strict prime conventions are
handled in the actual carrier identities.

The module also proves the bound for the literal
`jurkatRichertSourceMediumPrimes` sum:

$$
\sum_{q\in\mathcal Q(N)}\frac1q
\le\log(10/3)+\eta_*(L).
$$

[GRHH10MediumMass.lean](GRHH10MediumMass.lean) gives the numerical cap
121/100 and its aggregate adapter: if f(q) <= A/q with A >= 0 on the
actual medium-prime carrier, its sum is at most (121/100) A.
This supplies the harmonic-mass replacement for the former 4 L^2 bound;
the remaining source-dependent tail estimates are separate obligations.

[GRHH10Rankin.lean](GRHH10Rankin.lean) generalizes the actual pre-sieve
remainder assembly to every sigma >= 0. In particular,

$$
\sum_{d\in F,\ d>C}f(d)
\le C^{-\sigma}\sum_{d\in F}d^\sigma f(d)
$$

for nonnegative f and C > 0. It proves the weighted remainder truncation
with distribution range C D, as well as the exact finite Euler identity

$$
\sum_{d\mid Q}f(d)
=\exp\!\left(\sum_{p\mid Q}\log(1+f(p))\right)
$$

for squarefree Q and a nonnegative multiplicative arithmetic function.
It does not replace log(1+u) by u. The identities do not certify the
specific proposed finite moment values, or the desired tail prefactor.

These new analytic components use standard Lean axioms only. They add
no GRH assumption beyond the one already used by the full Chen route.

## Conditional coefficient certificates

[GRHH10BandBudget.lean](GRHH10BandBudget.lean) kernel-checks the generated
coefficient coupons for all 199 bands. The proposed base/medium losses,
radius coefficient and pair coefficient satisfy

$$
b_i\le0.068,\quad m_i\le1.12,\quad K_i\le8.06,\quad P_i\le0.495.
$$

Using the earlier exact arithmetic contract, `positive_of_band_counts`
proves that actual estimates with those coefficients and remainder cap
C5 <= 30,000,000 would imply

$$
R(N)\ge\frac{67}{4000}M(N)>0.
$$

The actual lower and triple inequalities are explicit hypotheses of this
theorem. The coefficient certificate does not discharge them. No interior
band is labelled as a proved Chen result in the experiment report.

## Numerical results

Each profile is optimized independently on every band, using fixed
parameters within that band. Tail/distribution envelopes are tested at
the left endpoint with their monotonicity side conditions. The prime
interval and grid errors decrease thereafter. The envelope values and
finite moment caps remain numerical proposals where not covered by the
new analytic lemmas above.

| Profile | Positive modeled bands | First positive L | Approximate H |
| --- | ---: | ---: | ---: |
| Retuned published-shaped envelopes | 14 / 199 | 139062 | 11.843 |
| Actual prime-mass cleanup; half moment | 22 / 199 | 128417 | 11.763 |
| Prime-mass cleanup; variable Rankin; retain Pan | 78 / 199 | 73536 | 11.206 |
| Targeted H10 package; existing pre-sieve endpoint | 199 / 199 | 22026 | 10 |
| Targeted H10 package; endpoint 300000 | 199 / 199 | 22026 | 10 |

These are numerical fits before replacing inherited source-mass,
denominator and interface thresholds. In particular, the first three rows
are not new numerical Chen cutoffs. Reoptimizing an envelope's parameters
also differs from simply applying the old fixed parameter choice.

The first band [22026,22247) is the worst modeled band for the recommended
H10 profile. Its parameters remain

$$
z=4000000,\quad\sigma=1/4,\quad
\theta=0.0073,\quad\delta=0.00234,\quad g=0.097.
$$

The model gives lower coefficient approximately 2.021368, triple
coefficient approximately 3.979828, and margin approximately **0.031454**.
The alternate smaller-product package has minimum modeled margin about
**0.022837**. Both have unproved analytic requirements.

## What finite banding helps, and what it does not

Finite banding gives an exact coverage/pasting architecture and allows
different parameters or analytic methods on different portions of the gap.
It does not make a false left-endpoint inequality true. The envelopes
tested here are already monotone beyond each left endpoint, so this first
experiment does not establish an additional gain merely from using an
upper endpoint. To obtain such a gain, a genuinely interval-dependent
analytic estimate would have to be added.

Nor does a band require testing all integers in it. Its representation
statement must be uniform over all integers in that band. The existing
large finite prime-count campaign is reused; no new zero campaign or
enumeration of integers up to exp(exp(10)) was run.

## Remaining requirements before H10 is proved

1. Certify the proposed finite Euler moment caps, using the new exact
   identity and a kernel-checked finite computation or analytic bound.
2. Finish source-tail aggregation with the new Rankin exponent and
   harmonic-mass bound. The recommended 16 L prefactor is still a strong
   unproved target, not an automatic consequence of the two new lemmas.
   The alternate 16 L^2 target also needs its smaller-endpoint product theorem.
3. Prove the specialized weighted distribution bound and the full
   convolution/QD remainder at the band parameters, replacing the
   39 log L range gate. Pointwise AP estimates do not suffice by themselves.
4. Prove the source-mass estimates at these smaller scales. Pay the
   denominator using a sharper singular-series bound such as S(N) <= 10L
   and a scale-dependent floor reserve. These remain unproved inputs to
   the H10 model.
5. Connect the improved interval error to both actual grid estimates,
   discharge the lower/triple hypotheses on every band, paste with the
   saved theorem, and run the complete Chen audit.

The most concrete next step is source-tail aggregation: the general
Rankin remainder and the actual harmonic-mass adapter are now available.
It will determine whether the linear-prefactor route is viable or the
smaller-endpoint quadratic alternative is preferable. The full weighted
convolution bound remains the other major mathematical risk.

## Reproduction

```powershell
node research/chen-grh/tools/ExperimentH10Bands.mjs
node research/chen-grh/tools/CheckH10BandExperiment.mjs
```

The generator rewrites the numerical report and the two generated Lean
files. Regeneration is not verification. To kernel-check the modules,
use the pinned source builder, serially on a machine with limited RAM:

```powershell
$env:CHEN_BUILD_TAG = 'grhhbands'
$env:CHEN_BUILD_JOBS = '1'
$env:CHEN_LEAN_MEMORY_MB = '6000'
node --expose-gc --max-old-space-size=4096 OpenAI/tools/build-source.mjs GRHH10BandBudget GRHH10Rankin GRHH10MediumMass
```

The component check record supplied with this experiment was produced
after invoking the same pinned Lean executable directly with the checked
434 object path. It records component source/object hashes, imported
local object hashes and axiom prints. No independent comparator or final
Chen audit is claimed for this experiment.
