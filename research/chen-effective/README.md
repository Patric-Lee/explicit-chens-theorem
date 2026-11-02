# Effective Chen investigation

Status: the explicit Siegel constant, finite counting endgame, numerical
high-conductor BV and elementary payments, finite BV assembly, and downstream
Chen distribution/triple residual payments are proved and compile-checked.
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
sources remain unchanged. The first research checkpoint was committed as
`ae118ce9` before the second pass described below.

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

## Second pass: numerical BV payments and propagation

All results in this section have only Lean's standard axioms. They have no
additional analytic axiom; their unsolved analytic inputs are theorem
parameters, not postulated facts.

### A fully numerical high-conductor bound

`ExplicitLogBounds.lean` proves

```
logPowerCutoff(k) = 3^(16*(k+1)^2)
N >= logPowerCutoff(k)  =>  log(N)^k <= sqrt(N).
```

It also proves the rational power-saving variant: if `m > 0`, `m*k <= t`,
and `N >= logPowerCutoff(t)`, then `log(N)^k <= N^(1/m)`. These replace actual
uses of little-o/eventual growth, rather than selecting witnesses from them.

`ExplicitBVHigh.lean` makes all three chosen high-conductor lanes finite:

```
B(A) = 3*A + 200
C(A) = 2*(A+50)
R(N) = floor(log(N)^C(A))
Q(N) = floor(sqrt(N)/log(N)^B(A))
Nhigh(A) = 3^(16*(6*A+401)^2)
```

For every `N >= Nhigh(A)`, the Type-I, Type-II, and small-lane constants are
respectively `2000`, `1000000000000000000`, and `10000`. The full weighted
high hybrid is bounded by

```
(1000000000000012000) * N/log(N)^A.
```

This high estimate is unconditional and has no unspecified starting point or
constant. Proof bodies preserve the repository's existing finite estimates;
their eventual growth premises are replaced by the numerical log lemmas.

`ExplicitBVPayload.lean` proves that the complete elementary BV correction
packet has constant `180` for `N >= 3`, in the appropriate modulus range.

### Finite full-BV assembly, with the two remaining analytic inputs visible

`ExplicitBVAssembly.lean` proves an estimate for the **actual** standard
prime-AP prefix-maximal error sum, with

```
KBV = 32*Kpsi + 4*Kprincipal + 1000000000000012180
NBV = max(Nhigh(A), nPsi, nPrincipal).
```

Here the required primitive estimate is the uniform prefix-amplitude bound
with conductor exponent `C(A)` and saving exponent `A+C(A)+5`, valid from
`nPsi`, with constant `Kpsi`. The principal input is the actual
`globalPartialSummationSource`, with saving exponent `A+3`, valid from
`nPrincipal`, with constant `Kprincipal`.

**This does not assert numerical values for those four low analytic data.**
The high and elementary sides are now numerical; the two low inputs remain
unproved in numerical form. The old asymptotic SW or MediumPNT theorem is not
used to pretend otherwise.

### Propagation into Chen's lower-sieve distribution term

`ExplicitChenLower.lean` fixes ordinary BV exponent `A=3`, hence `B=209` and
`C=106`. Its primitive input needs saving exponent `114`, and its principal
input needs saving exponent `6`.

For natural `m >= 3`, `d >= 1`, and an integer `b >= KBV`, set

```
epsilon = 1/m
delta = 1/d
Ndist = max(Nhigh(3), logPowerCutoff(m*209), logPowerCutoff(4),
            3^(4*b*d + 16*d + 1)).
```

Above this numerical additional cutoff, a finite BV input at `N` implies

```
jurkatRichertSourceRemainderSum N epsilon
    <= delta * S(N)*N/log(N)^2.
```

The proof pays both the source modulus-range inclusion and the genuine
exceptional-prime correction. `explicit_base_distribution_of_low_inputs`
connects the finite BV assembly directly to this statement. The full weighted
lower estimate still needs numerical sieve/Mertens normalization and the
varying-prime/prime-power inputs; it is not proved merely by this remainder
estimate.

### Propagation into Chen's triple bound and final representation theorem

`ExplicitChenTriple.lean` proves the endpoint complement and the paper-modulus
residual with coefficients `13` and `6`, respectively, for every

```
N >= 3^21904 = logPowerCutoff(36).
```

If the actual Selberg-square estimate has main coefficient `3.94033` and
error coefficient `Csquare`, valid above a numerical `nSquare`, then the
actual corrected triple estimate has coefficient **`Csquare+19`**, valid for

```
N >= max(nSquare, 3^21904).
```

`explicit_chen_from_square_estimates` carries this through the checked finite
counting endgame. Given the numerical weighted lower input starting at
`nLower` and an integer `B >= Csquare+19`, its final threshold is

```
max(9, nLower, nSquare, 3^21904, 3^(20000*B+1)).
```

The square constant and its numerical starting point are still required;
they have not been evaluated or replaced with an additional axiom.

## What remains before a numerical N0

| Stage | Existing seam | Numerical work still needed |
| --- | --- | --- |
| Quadratic L-value lower bound | `Siegel/Bombieri1965Theorem4SiegelLowerBound.lean` | Replaced here by explicit `c(eta)` under the local axiom. |
| Low-conductor primitive estimates | `LargeSieve/DirichLTwistedQuadraticPointwiseSiegelWalfisz.lean` and its nonquadratic counterpart | Bound contour/smoothing constants; replace the eventual scale/decay payments by explicit cutoffs. The quadratic exponent is already the formula `1/(4096*(C+D+1))`. |
| Low-conductor summation | `LargeSieve/StandardBVLowSiegelWalfiszProducer.lean` | Finite nonprincipal payment proved here. Still supply numerical primitive and principal/PNT inputs. |
| High-conductor BV and elementary packet | `ExplicitBVHigh.lean`, `ExplicitBVPayload.lean` | Completed with numerical constants and starting points. |
| Full BV and Liu-Pan distribution | `ExplicitBVAssembly.lean` and `SieveTheory/Distribution/LiuPan` | BV assembly now carries explicit data. Supply the two low analytic inputs numerically, then quantify the remaining weighted/Liu-Pan transformations. |
| Weighted lower estimate | `LinearSieve/JurkatRichert/JurkatRichert1965ChenRichertConsumer.lean` | Obtain a numerical `nLower`. Its Suzuki varying-family, Mertens/Euler-product, distribution, and prime-power limits currently hide rates. |
| Triple upper estimate | `ExplicitChenTriple.lean` and `Selberg/Liu/LiuSelbergCorrectedChenBridge.lean` | Residual constants are `13+6`, both paid from `3^21904`. Obtain numerical `nSquare` and `Csquare`, then take `B >= Csquare+19`. |
| Finite endpoint | This directory | Completed conditionally on those numerical analytic inputs. |

The Suzuki source explicitly uses `Tendsto` to absorb its error, independently
of Siegel ineffectivity (`Suzuki/SuzukiChenAdaptiveDepthAbsorption.lean`).
The triple producer explicitly chooses `Cend` and `Cpan` and joins several
eventual estimates. These are concrete reasons the single explicit Siegel
constant does not make the existing public theorem numerically explicit.
This table identifies known obligations; it is not a certificate that every
hidden asymptotic constant in the full analytic closure has been enumerated.

The next analytic stage is to supply numerical primitive SW and principal/PNT
data to the finite BV assembly. The principal route still invokes an
`IsBigO` witness from `MediumPNT`; the primitive route still chooses
contour/smoothing constants. Those need quantitative estimates. The single
Dirichlet axiom gives zero-freeness but does not itself provide those norm
estimates. Carry the resulting finite BV data through the remaining weighted
distribution and sieve normalizations, and use the endpoint only once its
numerical inputs have actually been proved.

## Reproduce

From the checkout, in PowerShell:

```powershell
& ./research/chen-effective/check.ps1
```

This checks only the nine research modules, in dependency order, treating warnings as errors,
writes `.olean` files and axiom reports under `.lake/build/chen-effective/`,
and audits local imports and the single added axiom. It does not rebuild the
Li-Liu development or alter the pinned dependency manifests. `LEAN_PATH` is
temporarily extended with the research artifact directory and restored by the
script, and each source uses this directory as its package root. The ordinary
default `lake build` does not include these research files.
