# Effective Chen investigation

Status: the explicit Siegel constant, finite counting endgame, and finite
nonprincipal low-conductor summation are proved and compile-checked.
**A closed numerical Chen threshold has not been obtained.** The analytic
starting points `nLower`, `nTriple`, and a numerical bound `B` for the triple
error constant remain unresolved. This directory does not change the main
libraries or claim those hypotheses have been discharged.

Base checkout: `9d4c3a4010d42aedd9e7231bf94386019cfffccc`.
Toolchain: `leanprover/lean4:v4.33.0-rc1`.

## Hypothesis and dependency boundary

`ExplicitSiegel.lean` contains exactly one added axiom:

```lean
axiom dirichlet_seven_eighths
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    χ.LFunction s ≠ 0
```

This matches the statement in
[DirichletSevenEighths.lean](https://github.com/openai/math/blob/main/lean/ComparatorChallenges/DirichletSevenEighths.lean).
On inspection, that file and
[QuasiRiemannHypothesis.lean](https://github.com/openai/math/blob/main/lean/ComparatorChallenges/QuasiRiemannHypothesis.lean)
contain `sorry` proofs. They are statement references, not proofs imported here.
Neither file nor any other OpenAI module has been added as a dependency.
No additional packages are required. Existing Lake manifests and production
sources remain unchanged.

The Dirichlet axiom directly excludes the quadratic exceptional zeros in the
Siegel argument. The zeta statement alone does not directly exclude zeros of
nonprincipal quadratic L-functions; this investigation does not assert an
implication from zeta nonvanishing to the Dirichlet hypothesis. The local axiom
also gives zeta nonvanishing away from its pole via the modulus-one character.

The project-side import closure contains one existing shared helper named
`MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDivisorMean`, through
the standard BV infrastructure. The Li-Liu 1+1.9 theorem modules are excluded.
This helper comes from the existing checkout, not from OpenAI.

## Proved results

### Explicit quadratic Siegel bound

For every real `eta > 0`, set

```
epsilon(eta) = min(1/16, eta/8)
c(eta) = epsilon(eta) / (4 * 648^(4 * epsilon(eta))).
```

`explicit_quadratic_L_one_lower_bound` proves

```
c(eta) * q^(-eta) <= Re(L(1, chi))
```

for every primitive nonprincipal quadratic character of nonzero modulus `q`.
The constant is explicit and positive. No unspecified neighborhood size or
exceptional-character witness occurs in its definition. The proof uses the
existing explicit positive-convolution estimate with cutoff `(648*q)^4`,
propagates the zeta sign along the zero-free real interval, and obtains
positivity of the quadratic L-function there from the single axiom.

`explicit_rawLandauSiegelLowerBound` supplies the existing raw interface.
`nonprincipal_source_from_explicit_siegel` and
`standardBV_from_explicit_siegel` plug it into the existing Siegel-Walfisz/BV
route without the ineffective fixed-witness Siegel theorem. Those interfaces
still have existential constants and eventual thresholds. They do not yield
a numerical BV threshold merely by changing their input.

The axiom reports for the explicit lower bound and the BV adapter contain
only `dirichlet_seven_eighths`, `propext`, `Classical.choice`, and `Quot.sound`.

### Numerical finite endgame

`NumericalThresholds.lean` has no added axioms. It proves:

* `half_le_liuUniversalProduct`: the universal Liu product is at least `1/2`.
  A finite product comparison telescopes to `(n+2)/(2*(n+1))`, then passes to
  the already established infinite-product limit.
* `half_le_liuSingularSeries`: consequently `S(N) >= 1/2` for every `N`.
* `inverse_log_remainder_le`: for `N >= 9`, `C <= B`, and
  `N >= 3^(20000*B+1)`, the remainder `C*N/log(N)^3` is at most
  `S(N)*N/(10000*log(N)^2)`.
* `explicit_representation_count`: given the two input estimates below,
  the actual public good-representation count is at least
  `0.67*S(N)*N/log(N)^2` above `chenCutoff`.
* `explicit_chen_of_estimates`: the same hypotheses give the literal
  prime-plus-prime-or-product-of-two-primes statement above `chenCutoff`.

The input estimates are precisely:

```
W(N) >= 2.6407 * S(N)*N/log(N)^2                    (N >= nLower, N even)
T(N) <= 3.94033 * S(N)*N/log(N)^2 + C*N/log(N)^3   (N >= nTriple, N even)
C <= B, with B a natural number.
```

Here `W` is `jurkatRichertWeightedCount` and `T` is
`correctedChenTriplePenalty`. The exact threshold is

```
chenCutoff nLower nTriple B = max 9 (max nLower (max nTriple (3^(20000*B+1)))).
```

The finite margin is `2.6407 - (3.94033 + 0.0001)/2 = 0.670485 > 0.67`.
The proof uses the existing corrected counting bridge, not an alternative
representation set. No classical choice from the existing existential Chen
theorem is presented as a numerical threshold.

### Finite low-conductor payment

`ExplicitLowConductor.lean` has no added axioms.
`low_scalar_envelopes_at_eight` proves, for every `N >= 8`,

```
Q = panModulusCutoff N B <= N,
lowConductorArithmeticMass N Q C <= 4*log(N)^(C+2),
conductorHarmonicFactor Q ^ 2 <= 4*log(N)^2.
```

Given the actual primitive-prefix estimate

```
amplitude(N,d,psi) <= K*N/log(N)^(A+C+5)
```

for every primitive nonprincipal character in the low-conductor range,
`explicit_low_conductor_payment` proves

```
2 * AbelAmplifier(N) * lowConductorPhysical(N,Q,C)
    <= 32*K*N/log(N)^A.
```

Thus if the primitive estimate is known for `N >= nPsi`, this summation step
works for `N >= max 8 nPsi`. It does not prove a numerical value for `nPsi`
or `K`, and it does not include the separate principal/PNT contribution.

## What remains before a numerical N0

| Stage | Existing seam | Numerical work still needed |
| --- | --- | --- |
| Quadratic L-value lower bound | `Siegel/Bombieri1965Theorem4SiegelLowerBound.lean` | Replaced here by explicit `c(eta)` under the local axiom. |
| Low-conductor primitive estimates | `LargeSieve/DirichLTwistedQuadraticPointwiseSiegelWalfisz.lean` and its nonquadratic counterpart | Bound contour/smoothing constants; replace the eventual scale/decay payments by explicit cutoffs. The quadratic exponent is already the formula `1/(4096*(C+D+1))`. |
| Low-conductor summation | `LargeSieve/StandardBVLowSiegelWalfiszProducer.lean` | Finite nonprincipal payment proved here. Still supply numerical primitive and principal/PNT inputs. |
| Full BV and Liu-Pan distribution | `LargeSieve/StandardBVFinalNonprincipalOnly.lean` and `SieveTheory/Distribution/LiuPan` | Propagate numerical constants and moduli-range thresholds, including the high-conductor route. |
| Weighted lower estimate | `LinearSieve/JurkatRichert/JurkatRichert1965ChenRichertConsumer.lean` | Obtain a numerical `nLower`. Its Suzuki varying-family, Mertens/Euler-product, distribution, and prime-power limits currently hide rates. |
| Triple upper estimate | `Selberg/Liu/LiuSelbergCorrectedChenBridge.lean` | Obtain `nTriple` and bound `Cend + Cpan + 6` by a concrete integer `B`, with the paper-modulus and complement residual cutoffs. |
| Finite endpoint | This directory | Completed conditionally on those numerical analytic inputs. |

The Suzuki source explicitly uses `Tendsto` to absorb its error, independently
of Siegel ineffectivity (`Suzuki/SuzukiChenAdaptiveDepthAbsorption.lean`).
The triple producer explicitly chooses `Cend` and `Cpan` and joins several
eventual estimates. These are concrete reasons the single explicit Siegel
constant does not make the existing public theorem numerically explicit.
This table identifies known obligations; it is not a certificate that every
hidden asymptotic constant in the full analytic closure has been enumerated.

A practical next stage is a numerical BV contract carrying an explicit
constant and starting point for each requested exponent. Prove the principal,
nonprincipal low, and high-conductor estimates against that contract, then
carry those data through the two sieve estimates above. Use the finite endpoint
here only after the three numerical inputs have actually been proved.

## Reproduce

From the checkout, in PowerShell:

```powershell
& ./research/chen-effective/check.ps1
```

This checks only the three research modules, treating warnings as errors,
writes `.olean` files and axiom reports under `.lake/build/chen-effective/`,
and audits local imports and the single added axiom. It does not rebuild the
Li-Liu development or alter the pinned dependency manifests. The ordinary
default `lake build` does not include these research files.
