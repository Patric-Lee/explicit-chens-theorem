# Effective Chen investigation

Status: the explicit Siegel constant, finite counting endgame, numerical
high-conductor BV and elementary payments, numerical primitive low-conductor
estimates, numerical principal PNT, numerical BV, and downstream
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
| Low-conductor primitive estimates | `NumericalLowConductor.lean` | Completed under the local axiom: `Kpsi(C)=10^11*(C+1)`, `nPsi(D)=3^(16*(128*(D+1)+1)^2)`. Covers all prefixes and both character classes. |
| Low-conductor summation and principal PNT | `NumericalPrincipalPNT.lean`, `ExplicitLowConductor.lean` | Completed. Principal source constant `5*10^11`, with threshold `3^(16*(128*(D+1)+1)^2)`. |
| High-conductor BV and elementary packet | `ExplicitBVHigh.lean`, `ExplicitBVPayload.lean` | Completed with numerical constants and starting points. |
| Full BV and weighted distribution | `NumericalBV.lean`, `NumericalUpperDistribution.lean` | Ordinary BV and the Richert weighted/varying-prime distribution input are numerical. The Liu-Pan convolution branch for the triple estimate remains unfinished. |
| Weighted lower estimate | `NumericalLowerEndpoint.lean` and `LinearSieve/JurkatRichert/JurkatRichert1965ChenRichertConsumer.lean` | Obtain numerical lower/upper density producers and `nLower`. Distribution, the Suzuki coordinate gate, and endpoint/prime-power losses are numerical. The Suzuki constants, density normalization, and prime-q main-term transfer still need rates. |
| Triple upper estimate | `ExplicitChenTriple.lean` and `Selberg/Liu/LiuSelbergCorrectedChenBridge.lean` | Residual constants are `13+6`, both paid from `3^21904`. Obtain numerical `nSquare` and `Csquare`, then take `B >= Csquare+19`. |
| Finite endpoint | This directory | Completed conditionally on those numerical analytic inputs. |

The Suzuki source explicitly uses `Tendsto` to absorb its error, independently
of Siegel ineffectivity (`Suzuki/SuzukiChenAdaptiveDepthAbsorption.lean`).
The triple producer explicitly chooses `Cend` and `Cpan` and joins several
eventual estimates. These are concrete reasons the single explicit Siegel
constant does not make the existing public theorem numerically explicit.
This table identifies known obligations; it is not a certificate that every
hidden asymptotic constant in the full analytic closure has been enumerated.

The principal/PNT and primitive inputs are now supplied numerically to the
finite BV assembly. The new production proof does not select any constants or
thresholds from the existing `MediumPNT` asymptotic theorem.
Carry the resulting finite BV data through the remaining weighted
distribution and sieve normalizations, and use the endpoint only once its
numerical inputs have actually been proved.

## Numerical primitive checkpoint

`NumericalSmoothing.lean` constructs a rational polynomial kernel with mass
one, support `[1/2,2]`, and derivative norm at most `128`.
`NumericalMellin.lean` proves Mellin constant `768` and smoothing-removal
constant `60`; `NumericalRightTail.lean` exposes the quantitative tail proof
with a caller-supplied Mellin bound, giving constant `4608` here.

`NumericalLogDerivative.lean` proves a disk estimate using Borel--Caratheodory
and Schwarz. `NumericalDirichletStrip.lean` applies it under the local axiom:

```
15/16 <= re(s) <= 2
norm(L'(s,chi)/L(s,chi)) <= 8192*log(16*q*(abs(im(s))+4))
```

`NumericalPrimitiveContour.lean` supplies an explicit finite contour bound.
`NumericalPrimitivePower.lean` fixes the right displacement `1/1024`, height
`X^(1/32)`, and smoothing width `X^(-1/128)`, obtaining for every `X >= 9`:

```
norm(psi(X,chi)) <=
 (10^10 + 2*10^8*log(16*q*(X^(1/32)+4)) + 60*log(X))*X^(127/128).
```

`NumericalLowConductor.lean` controls every endpoint `y <= N`, including
small endpoints, and proves the actual primitive prefix-amplitude bound
with `Kpsi(C)` and `nPsi(D)` above, uniformly for `q <= log(N)^C`.
`numerical_primitive_low_conductor_cutoff` uses the repository's exact
`logConductorThreshold` interface. There is no remaining primitive
smoothing, contour, compactness, or eventual-payment witness in this result.

## Numerical principal PNT and BV

`NumericalZetaStrip.lean` proves the regularized-zeta bound

```
norm(zeta_1'(s)/zeta_1(s)) <= 8192*log(32*(abs(im(s))+6)^2)
```

on the same strip, where `zeta_1(s)=(s-1)*zeta(s)` with the pole removed.
It also proves the exact logarithmic-derivative identity including the pole
term. `NumericalContourEdges.lean` bounds the actual zeta logarithmic
derivative by `8192*log(32*(T+6)^2)+16` on the left and horizontal contour
edges. `NumericalPrincipalContour.lean` checks the residue identity giving
the main term `Mellin(Smooth1)(1)*X`.

`NumericalResidueAssembly.lean` and `NumericalPrincipalSmoothed.lean` assemble
the contour error, keeping the exact pole main term. `NumericalMainTerm.lean`
proves `norm(Mellin(Smooth1)(1)-1) <= 2*epsilon` for `0 < epsilon < 1`.
It uses the kernel's unit mass and `abs(log(x)) < 1` on its support.

`NumericalPrincipalPower.lean` fixes the same contour parameters as the
primitive proof. For every real `X >= 9` it proves

```
norm(lambdaCharacterPrefix(floor(X),1,1) - X) <=
 (3*10^10 + 2*10^8*log(32*(X^(1/32)+6)^2) + 60*log(X))*X^(127/128).
```

`NumericalPrincipalElementary.lean` bounds the Abel amplifier and the
discrete-to-true-li discrepancy by `4`, including endpoints `0` and `1`.
The reciprocal-log integrals crossing the singularity at `1` are checked
to be nonintegrable, so their total Bochner integral is zero under the
repository's existing definitions. This endpoint fact does not invoke an
unspecified numerical bound.

`NumericalPrincipalPNT.lean` controls every integer prefix through `N` and
proves the exact input consumed by BV:

```
N >= principalNumericalThreshold(D) = 3^(16*(128*(D+1)+1)^2)
globalPartialSummationSource(N) <= 500000000000*N/log(N)^D.
```

`NumericalBV.lean` discharges both analytic hypotheses of `ExplicitBVAssembly`.
For every natural `A`, its constant and threshold are

```
K_BV(A) = 32*10^11*(2*A+101) + 4*(5*10^11) + 1000000000000012180
N_BV(A) = 3^(16*(384*A+13569)^2).
```

`numerical_BV` bounds the actual sum of prime-AP prefix-max errors through
the repository's modulus cutoff with exponent `3*A+200`, by
`K_BV(A)*N/log(N)^A` for all `N >= N_BV(A)`.
In particular, `K_BV(3)=1000344400000012180` and
`N_BV(3)=3^3467325456`. No unknown analytic constant or starting point remains
in this BV statement. The weighted lower sieve and triple-square producer
remain separate obligations before a fully numerical Chen threshold.

## Numerical Richert distribution and lower-sieve checkpoint

`NumericalWeightedMass.lean` proves an elementary totient-weighted moment:

```
sum(d in S, k^omega(d)/phi(d)) <= (1+log(Q))^(2*k)
```

for squarefree `S` inside `[1,Q]`. It uses the existing ordered-divisor mean
helper already in the research import closure. No additional Li-Liu theorem
module is imported. A finite Cauchy inequality uses `phi(d)` directly, and
`NumericalWeightedEnvelope.lean` proves
`phi(q)*standardPrimeAPMaxError(N,q) <= 12*N` for `N >= 9`, `1 <= q <= N`.
Thus the old unspecified Mertens/totient-envelope constants are unnecessary
for this Richert distribution route.

`NumericalWeightedDistribution.lean` takes ordinary BV saving `U=2*A+18`.
For `epsilon=1/m`, `m>0`, it proves the actual reduced combined-modulus sum

```
jurkatRichertSourceReducedWeightedBVSum(N,1/m) <= Kweight(A)*N/log(N)^A
Kweight(A) = 3145728*(K_BV(2*A+18)+1)
Nweight(A,m) = max(N_BV(2*A+18), logPowerCutoff(m*(6*A+254))).
```

`NumericalVaryingCorrections.lean` retains the exact truncated divisor
carriers rather than enlarging to all divisors of the sifting product.
It proves the actual nonreduced/source-support correction is at most
`3000*N^(9/10)*log(N)^7` for `N >= 9`, `epsilon >= 0`.

Set the explicit integer

```
b = 3145728*(1000478800000012180+1)+3000.
```

`NumericalUpperDistribution.lean` bounds the actual varying-q upper remainder
by `(1/d)*S(N)*N/log(N)^2` for `m,d>0`, even `N`, and

```
N >= max(max(Nweight(3,m),logPowerCutoff(100)), 3^(2*b*d+1)).
```

This completes the Richert distribution input needed by the lower sieve.
It does not prove the distinct Liu-Pan convolution distribution input for
the triple-square remainder.

For the lower sieve, `NumericalSuzukiGate.lean` proves the actual Chen-to-Suzuki
source-coordinate gate from `N >= 3^381469726563`. The scalar error payment in
`NumericalSuzukiAbsorption.lean` is finite: an amplitude bounded by the integer
`M` is absorbed below `1/r` from
`D >= 3^max(152587890625,4096*(M+1)^2*r^2)`, uniformly for `0<s<=5`.

`NumericalSuzukiHat.lean` now bounds the actual Section 13 hat functions:
`0 <= H(sign,s) <= 4` for `s >= 2`, hence `s*H(sign,s) <= 20` for
`2 <= s <= 5`. If the remaining Suzuki constant `C <= c` and local-product
constant `K <= k`, with natural `c,k` and `k >= 1`, the actual amplitude is
at most `M = 20*c*3^k`. For every depth, the actual Chen-level error is below
`1/r` once

```
N >= 3^(5*max(152587890625,4096*(20*c*3^k+1)^2*r^2)).
```

Numerical caps for `C` and `K` are still required; the hat-function amplitude
itself no longer contributes an unnamed constant.

`NumericalLowerFactor.lean` replaces qualitative continuity near `s=5` by
`f(5)-3*(5-s) <= f(s)` on `[4,5]`, for the actual dimension-one lower
linear-sieve factor. Choosing `epsilon=1/(60*r)`, `r>0`, gives
`0 < epsilon < 1/10` and `f(5)-1/(2*r) <= f(chenS(epsilon))`.
This quantifies the lower-factor loss; the remaining coefficient losses
must still be allocated before fixing the final common epsilon.

`NumericalMertens.lean` proves, for every real `x >= 3^1056784`,

```
abs(theta(x)-x) <= 300000000000*x/log(x)
abs(sum(p<=x,1/p) - (log(log(x))+B)) <= 900000000000/log(x).
```

Here `B` is the existing canonical Mertens constant. It cancels in the
checked interval version: for `3^1056784 <= w <= z`, the reciprocal-prime
sum over `(w,z]` differs from `log(log(z))-log(log(w))` by at most
`1800000000000/log(w)`. These are numerical consequences of the one local
Dirichlet axiom, using the already proved principal PNT. Product and
singular-series normalization still need to be deduced from them.

`NumericalLowerEndpoint.lean` pays boundary and prime-power losses from

```
Nend = max(2^110+1, logPowerCutoff(30), 3^2400000).
```

A source weighted coefficient `2.64075` then gives the required production
coefficient `2.6407`. More precisely, `numerical_lower_from_density_bounds`
reduces the remaining task to finite actual-candidate and medium-prime
aggregate bounds with margins `1/40000` and `1/20000`, respectively.
The following numerical producers are still unfinished:

- numerical caps for the Suzuki lower/upper density constants and local-product constant;
- product/singular-series normalization and prime-q main-term transfer rates,
  now with a numerical reciprocal-prime Mertens estimate available;
- a common rational epsilon meeting all coefficient error budgets, beyond
  the quantified lower-factor loss above.

There is still no numerical `nLower`, and no fully numerical Chen `N0`.

## Reproduce

From the checkout, in PowerShell:

```powershell
& ./research/chen-effective/check.ps1
```

After an interrupted check, `-FromModule ModuleName` resumes compilation at
that module; the full import and local-axiom audit still runs.

This checks only the thirty-eight research modules, in dependency order, treating warnings as errors,
writes `.olean` files and axiom reports under `.lake/build/chen-effective/`,
and audits local imports and the single added axiom. It does not rebuild the
Li-Liu development or alter the pinned dependency manifests. `LEAN_PATH` is
temporarily extended with the research artifact directory and restored by the
script, and each source uses this directory as its package root. The ordinary
default `lake build` does not include these research files.
