# Effective Chen investigation

Status: the actual medium-prime aggregate upper estimate, the weighted lower
estimate, and the square/triple estimate are proved at closed numerical
cutoffs. **A closed numerical Chen threshold is now proved under the single
local Dirichlet seven-eighths axiom.** `NumericalChenCutoff.lean` supplies
`numerical_chen` and the quantitative representation-count theorem. There
are no remaining analytic estimates as hypotheses of these final theorems.
The threshold is an explicit formula built from the numerical constants
below; no unspecified or chosen analytic threshold occurs in it.

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
lower estimate also uses the numerical sieve/Mertens normalization and the
varying-prime/prime-power inputs completed in the modules below.

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

The completed `NumericalNSquare.lean` instantiates this bridge numerically,
as described below: `nSquare=3^(3^4000000000000)` and `B=10^40`.

## Numerical closure status

| Stage | Existing seam | Numerical status |
| --- | --- | --- |
| Quadratic L-value lower bound | `Siegel/Bombieri1965Theorem4SiegelLowerBound.lean` | Replaced here by explicit `c(eta)` under the local axiom. |
| Low-conductor primitive estimates | `NumericalLowConductor.lean` | Completed under the local axiom: `Kpsi(C)=10^11*(C+1)`, `nPsi(D)=3^(16*(128*(D+1)+1)^2)`. Covers all prefixes and both character classes. |
| Low-conductor summation and principal PNT | `NumericalPrincipalPNT.lean`, `ExplicitLowConductor.lean` | Completed. Principal source constant `5*10^11`, with threshold `3^(16*(128*(D+1)+1)^2)`. |
| High-conductor BV and elementary packet | `ExplicitBVHigh.lean`, `ExplicitBVPayload.lean` | Completed with numerical constants and starting points. |
| Full BV and weighted distribution | `NumericalBV.lean`, `NumericalUpperDistribution.lean`, `NumericalPanWeighted.lean` | Completed for ordinary BV, the Richert weighted/varying-prime distribution input, and the Liu-Pan convolution branch used for the triple bound. |
| Weighted lower estimate | `NumericalLowerEndpoint.lean` and `LinearSieve/JurkatRichert/JurkatRichert1965ChenRichertConsumer.lean` | Completed: `NumericalBaseCandidates.lean` and `NumericalMediumAggregate.lean` prove both actual source bounds, then `numerical_weighted_lower` at the closed cutoff `nLower`. |
| Triple upper estimate | `NumericalNSquare.lean` | Completed: `nSquare=3^(3^4000000000000)`, actual triple coefficient `3.94033`, and error coefficient at most `B=10^40`. |
| Finite endpoint | `NumericalChenCutoff.lean` | Completed under the single local axiom: closed `N0`, prime-plus-almost-prime representation, and coefficient `0.67` in the representation count. |

The Suzuki source explicitly uses `Tendsto` to absorb its error, independently
of Siegel ineffectivity (`Suzuki/SuzukiChenAdaptiveDepthAbsorption.lean`).
The original triple producer chooses `Cend` and `Cpan` and joins several
eventual estimates; the completed numerical research branch now replaces
those selections. The numerical lower branch is now completed as well in
`NumericalMediumAggregate.lean`, and the final closure is below.
The final theorem's axiom report records the logical boundary: the standard
Lean axioms and the one existing local Dirichlet axiom.

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
Dirichlet axiom, using the already proved principal PNT.

## Numerical lower-source normalization

The lower-source product and singular-series normalization now have explicit
error budgets. For a positive natural `r`, define

```
P(r) = max(3^1056784, 3^(1800000000004*r))
Nproduct(r) = (P(r)+1)^10
Nseries(r) = max(2^110+1, (80*r+3)^10)
Nmass(r) = max(Nproduct(r), Nseries(r)).
```

`NumericalMertensProduct.lean` proves
`abs(primeProduct(n)*log(n)*exp(gamma)-1) <= 1/r` for `n >= P(r)`.
It uses the existing exact Euler--Mascheroni constant identity and the
explicit `2/n` logarithmic-correction tail, without choosing any new
asymptotic witnesses.

`NumericalGoldbachProduct.lean` transfers the lower bound to the literal
source cutoff `z=floor(N^(1/10))+1`. For even `N >= Nproduct(r)`,

```
10*(1-1/r)*exp(-gamma)*S_truncated(N,z-1)/log(N) <= V(N,z).
```

`NumericalSingularNormalization.lean` proves, for even `N >= Nseries(r)`,
`2*S_Liu(N) <= (1+1/r)*S_truncated(N,z-1)`. It quantifies the existing
ten-large-prime-divisor tail estimate and the one-point cutoff correction.
This part is elementary and uses no Dirichlet axiom.

Combining both with the finite logarithmic-integral lower bound,
`NumericalSourceMass.lean` proves, for even `N >= Nmass(r)`,

```
(20*exp(-gamma)-40/r)*S_Liu(N)*N/log(N)^2
  <= sourceSieve.totalMass * sieveProductPrimeFactors(sourceSieve).
```

The concrete specialization `r=1600000` pays a source-mass coefficient
loss of `1/40000` at the displayed numerical threshold. This is a mass
normalization estimate; the lower-density factor and its error must still
be combined with it to obtain the candidate-count coefficient.

## Suzuki constant caps

The local-product constant now has a fixed numerical choice. Define

```
nstar = 3^1056784
A = (4*nstar + 900000000006)*nstar
E = 4*A + 52
Knum = (E+2)*3^(2*E).
```

`NumericalMertensGlobal.lean` proves the reciprocal-prime Mertens error is
at most `A/log(n)` for **every** integer `n >= 2`, using elementary bounds
below `nstar` and the previous numerical Mertens estimate above it.
`NumericalGoldbachInterval.lean` gives the resulting real-endpoint inverse
Goldbach-factor interval bound, retaining the closed lower endpoint.
`NumericalLocalProduct.lean` proves `2 <= Knum` and

```
HasDimensionOneLocalProductBound (jurkatRichertSourceBoundingSieve N) Knum
```

for every `N`. Thus the Suzuki local-product input needs no existential
choice or starting threshold. The large constants are kept symbolic in
Lean; their displayed formulas contain only numerical arithmetic.

`NumericalSuzukiNormalization.lean` proves the depth-one constant at
`Delta=1/2` is at most `36`, and the Claim-14.5 normalization at `d=16`
is at most `4*C145` for nonnegative `C145`. Its finite denominator bound
is `sourceSigma(2,16) >= 1/2`.

`NumericalSuzukiCaseOne.lean` exposes the literal coefficient `1` constructed
by the Case-B source proof and propagates it through the strict and even
Case-I producers. Thus `CBstrict=CBeven=1` can be used. Their source-large-log
thresholds remain existential; numerical coefficients do not by themselves
make those thresholds numerical.

`NumericalSuzukiLowStripScalar.lean` removes the separate low-strip eventual-K
and bounded-K witnesses. For every nonnegative `C1`, every `K>=2`, and every
natural `D>=2` with `log(D)<=C1*K^7`, it proves the actual odd low-strip
Claim-14.5 estimate with

```
Clow(C1) = 9000*C1^6*88!.
```

The proof bounds the scalar by `9000*log(D)^6*K^2` and uses the exponential
series term of order `88` to pay `K^44`. It involves no compactness-selected
minimum or unspecified analytic endpoint.

`SuzukiCoefficientAssembly.lean` combines these producers with the actual
all-depth moving-domain theorem at `(d,Delta,Theta)=(16,1/2,7)`. Its coefficient
is the explicit formula

```
C(C145,C1) = max(36, 4*C145, 36000*C1^6*88!).
```

This generic-in-K assembly selects a shared `C1min` and the complete
Claim-14.5 coefficient `C145` existentially. By itself it does not
give a closed numerical final `C`. The checked cap interface says that
`0<=C1<=b` and `C145<=a` suffice for

```
C <= max(36, 4*a, 36000*b^6*88!).
```

The completed fixed-K route below avoids the separate unknown `a` and
proves numerical admissibility of its shared separator.

## Explicit hat lower bounds and fixed-K assembly

`NumericalHatCompact.lean` replaces the compactness-selected positive minimum
by the formula

```
e(m) = 1 / (8*m^2*[2*(m+1)]^(2*m)),   m >= 3.
```

Both normalized Section-13 hat functions are at least `e(m)` on `[2,m]`.
The proof uses the tail-integral identity on half-step windows and finite
induction, uniformly for every normalized `Section13HatContract H 2`.
`NumericalHatLower.lean` deduces the explicit coarse lower profile
`exp(-8*s*log(6*s)) <= H(sign,s)` for all `s >= 2`.

For a natural log budget `Q`, set

```
M(Q) = 1679616*Q + 6
eps(Q) = min(1, 2*e(M(Q))).
```

`NumericalQuotientEnvelope.lean` proves `eps(Q)>0` and bounds the actual
error envelope below by `eps(Q)`, for every depth, every `s>=2`, and every
integer `D>=2` with `log(D)<=Q`. Above `M(Q)` the envelope is at least `1`.
No compactness minimum or qualitative tail cutoff is used in this result.

`NumericalCaseABounded.lean` retains the legacy fixed-quotient coefficient,
using `Q(q)=ceil(log(q))`. The active bounded-K assembly now uses the joint
envelope and one uniform logarithmic coefficient described below; it does
not use the legacy finite quotient sum. For `A=C1*Kmax^7`, write

```
B=max(1,A), R=2*B*(1+2*Kmax)
r=6*(1+max(0,A))^(1/8), f=exp(-8*r*log(6*r))
CBounded(C1,Kmax)=exp(sqrt(Kmax))*7*R^3*B^4/f.
```

For `C1>=0` and `1<=K<=Kmax`, this proves the actual bounded-K Case-A
inequality uniformly in the bounding sieve. The closed numerical `nLower`
is assembled below. No simplified bound on
its total number of exponential layers is asserted here.

`SuzukiFixedKAssembly.lean` fixes `K` before the sieve family varies and uses
this bounded-K estimate for Case A and coefficient `1` for Case B. Thus it
bypasses the qualitative large-K thresholds `Klow,Khigh`. It proves the
actual all-depth theorem with

```
C145(C1,K) = max(1, CBounded(C1,K))
Cfixed(C1,K) = max(36, 4*C145(C1,K), 36000*C1^6*88!).
```

`source_suzuki_coefficient_formula` specializes this to the actual Jurkat--Richert
hat functions and Chen source family at the already numerical `Knum`.
That earlier theorem obtains `C1min` existentially. The strengthened theorem
`source_suzuki_fully_numerical` in `NumericalSuzukiC1.lean` now supplies its
closed numerical value and closes the final Suzuki coefficient as well.

## Numerical subconditions for the shared C1

`NumericalRealLogBounds.lean` extends the explicit logarithmic payments to
real endpoints. In particular these payments can be applied to `x=log(D)`;
no integer-rounding or eventual witness is introduced for that substitution.

`NumericalC1Scalar.lean` proves the literal Case-I (14.23) scalar condition
for `K,D>=2`, `C1>=3^9461776`, and `C1*K^7<log(D)`:

```
K^2 * sourceSigma(D,16)^3 * log(exp(1)*sourceSigma(D,16)) * log(log(D))
  / log(D)^(1/2) <= 1.
```

The parameter margin is `1/2-(2/7+3/16)=3/112`. Its explicit logarithmic
payment is `32*log(x)^5 <= x^(3/224)` for `x>=3^9461776`.
This removes the `Xlog` little-o witness from this scalar subcondition.

`NumericalFiniteHat.lean` proves the Section-13 endpoint slack is at least
`1/72`, by integrating the initial-strip bound over `[3,4]`. It propagates
that bound through the full finite-depth induction to give the literal
coefficient `L=144`. Both the strict predecessor estimate and the closed
even endpoint are checked with this same coefficient.

`NumericalC1Order.lean` proves source-order absorption with the canonical
midpoint strict factor whenever `A<=a`, natural `a`, and
`C1>=3^(4*a+1)` under the same source-large-log condition. With `L=144`
and Case-B coefficient `1`, the actual endpoint amplitude is at most
`1+300*R`. Thus a numerical reverse-ratio cap `R<=r` would give the
checked order cutoff `C1>=3^(1200*r+5)`.

## Completed numerical shared C1

`NumericalSuzukiC1.lean` defines the closed expression

```
numericalSuzukiC1 = max(1, caseBSourceC1, caseIStrictC1, caseIEvenC1, caseIIC1).
numericalChenSuzukiCoefficient = Cfixed(numericalSuzukiC1, Knum).
```

Every constituent is a displayed numerical formula, independent of the sieve,
hat functions, recursion depth, and varying parameters. These formulas use
rational numbers, integer powers, logarithms, exponentials, real powers,
maxima, and natural ceilings. No unspecified analytic constant or
compactness-selected minimum remains in them. The bounded-K coefficient
uses a single uniform logarithmic formula, with no finite quotient sum.

The new proofs supply:

- Comparison `Qhat <= 51200000000 * T` and reverse-ratio cap
  `r = 51200000000 * (800 * 22^20 + 75)`.
- A forward majorant with `cMinus=1152`, `A=2`, cutoff `exp(2309)`.
- The sharp lower profile with coefficient `60000000000` from `s=20000`,
  and an explicit source-large-log Case-B cutoff.
- Numerical compact derivative and moving source-range bounds, all three
  clauses of Claim 14.6, and the resulting contraction and error transport.
- Numerical strict/even Case-I separators and a numerical Case-II separator,
  including finite endpoint bounds `864` and `576`.

`numerical_fixedK_suzuki` proves admissibility for every separator at least
`numericalSuzukiC1`. `source_suzuki_fully_numerical` specializes at that
displayed value to the actual Jurkat--Richert hats and Chen source sieve,
uniformly for every depth `N>=1`. Its axiom report is exactly `propext`,
`Classical.choice`, `Quot.sound`, and the existing local
`dirichlet_seven_eighths`. There are no new axiom declarations, OpenAI
imports, or external dependencies.

`NumericalLowerEndpoint.lean` pays boundary and prime-power losses from

```
Nend = max(2^110+1, logPowerCutoff(30), 3^2400000).
```

A source weighted coefficient `2.64075` then gives the required production
coefficient `2.6407`. More precisely, `numerical_lower_from_density_bounds`
uses finite actual-candidate and medium-prime aggregate bounds with margins
`1/40000` and `1/20000`, respectively. The candidate bound is now proved in
`NumericalBaseCandidates.lean`; `numerical_lower_from_medium_prime_bound`
leaves only the medium-prime aggregate as its analytic hypothesis.
The numerical upper-product normalization, prime-q transfer, and upper-sieve
epsilon/error budgets are now supplied by the modules in the completed
medium-prime closure below. `numerical_weighted_lower` and `numerical_chen`
discharge the formerly conditional lower estimate and Chen endpoint.

## Numerical Selberg remainder and triple error coefficient

`NumericalSelbergRemainder.lean` proves a numerical bound for the actual signed
Selberg remainder, for every admissible lambda and epsilon `1/m`:

```
|R(N,1/m,lambda)| <= CRem(A) * N / log(N)^A
N >= selbergRemainderThreshold A m.
```

Both the coefficient and threshold are displayed formulas. The proof includes
the moving principal convolution PNT, actual-prime primitive prefixes at `N/a`,
low-conductor deletion and harmonic payment, the high bilinear/Perron source,
cofactor induction, the actual unweighted convolution sum, weighted Cauchy,
source-window support, strict modulus cutoffs, normalization to `li_2`, and
the noncoprime `R1` correction.

The high source uses the explicit real primitive large-sieve coefficient
`8+2*pi` and complex coefficient `2*(8+2*pi)`. It does not bound an arbitrary
chosen large-sieve witness. The weighted source uses a totient envelope with
coefficient `6 + liuLogarithmicIntegralUpperConstant(kappa)/log(2)` and the
already numerical divisor moment. Thus no selected reciprocal-totient or
Mertens coefficient enters these new numerical formulas. Its unweighted saving
is `2*A+20`, and the source cutoff exponent is `2*A+28`.

In `NumericalSquareConstants.lean`:

```
numericalSquareError = CRem(3)
numericalTripleErrorCap = 10^40
numericalSquareError + 19 <= numericalTripleErrorCap.
```

`NumericalSquareAssembly.lean` fixes `epsilon=1/10000000000` and propagates
the numerical remainder through the square expansion and corrected Chen
triple penalty. The triple coefficient is `3.94033`, with error coefficient
at most `10^40`. This intermediate assembly has two finite main-term premises:

- the denominator bound
  `log(N)/((8+1/10000000)*S(N)) <= liuSelbergDenominator N epsilon`;
- the genuine-li prime-pair bound
  `LiuGenuineLiWeightMainSumBound 2 (0.49254+1/10000000) N`.

Both premises are discharged numerically by the completed `NumericalNSquare`
assembly below. The weighted lower estimate and its numerical `nLower` are
now also completed, giving the closed Chen `N0` in the final module.

Validation for the remainder checkpoint: all 21 modules passed a batch rerun
with warnings treated as errors, including the full local import/axiom audit,
after `lake.exe` was allowlisted in Windows application control.

## Numerical Selberg denominator

`NumericalSelbergDenominatorClosed.lean` proves, for every even integer

```
N >= 3^(3^4000000000000),
```

the exact required denominator bound at `epsilon=1/10000000000`:

```
log(N)/((8+1/10000000)*S(N)) <= liuSelbergDenominator N epsilon.
```

The numerical ingredients are:

- The fourth-root Euler mass `sum_d |h_2(d)| d^(1/4) <= exp(29)`, proved
  by a finite smooth-number Euler-product majorant and the numerical
  `zeta(3/2) <= 3` integral comparison.
- Universal absolute Euler mass at most `exp(29)` and logarithmic moment
  at most `4*exp(29)`.
- Prime-divisor product at most `54*(1+log log N)` and prime-divisor
  logarithmic moment at most `3*(1+log log N)^2`, at an explicit cutoff.
  The latter uses an elementary harmonic bound, without a Mertens witness.
- Combined denominator error numerator at most
  `10^24*(1+log log N)^6`, normalized error at most `10^-12`, and the
  finite correction for the floored moving Selberg cutoff.

The threshold is deliberately generous. `numericalDenominatorThreshold_eq`
certifies its literal integer-tower formula. Internal opaque certificates
keep enormous integers symbolic during kernel checking; their proved
equalities specify exact numerical values, with no choice or new axioms.

`numerical_square_from_prime_pair` discharges the denominator in the
intermediate square assembly. The final assembly below also discharges the
prime-pair premise and proves that all auxiliary thresholds lie below the
same integer tower.

All eight denominator modules passed the batch check with warnings treated as
errors. The full import/axiom audit also passed: the single existing local
Dirichlet axiom, zero OpenAI imports, and zero Li-Liu theorem imports.

## Completed numerical nSquare and triple estimate

`NumericalNSquare.lean` defines and proves the literal numerical value

```
nSquare = 3^(3^4000000000000).
```

For every even `N >= nSquare`, `numerical_square_bound` proves the actual
optimal Selberg square estimate, with no remaining analytic hypotheses:

```
Square(N) <= 3.94033*S(N)*N/log(N)^2 + numericalSquareError*N/log(N)^3.
```

At the same cutoff, `numerical_triple_bound` proves

```
correctedChenTriplePenalty N
  <= 3.94033*S(N)*N/log(N)^2 + 10^40*N/log(N)^3.
```

The last prime-pair step uses the fixed logarithmic grid `n=10^12`.
The already finite mesh-error bound is `759/n`. The numerical Mertens
estimate gives interval error `18000000000000/log(N)` uniformly over all
grid endpoints; summing rectangle errors gives
`105*n^2*18000000000000/log(N)`. The proved finite prime-pair threshold
ensures `log(N) >= 10^80`, paying this error by `10^-8`. Together with the
mesh error, the normalized proxy is at most `0.49254+2*10^-8`.

For the genuine logarithmic integral, an elementary split at `sqrt(x)`
proves `|li_2(x)-x/log(x)| <= 10*x/log(x)^2` above a numerical cutoff.
The proxy bound itself bounds the exact reciprocal pair mass by `1`,
avoiding the old chosen Mertens pair constants. Its summed correction is
at most `10^-8*N/log(N)`. This proves the required genuine-li coefficient
`0.49254+10^-7`.

`NumericalSquareThresholdCap.lean` bounds the entire numerical remainder
threshold by `3^(10^80)`. The final proof shows that both this threshold
and the prime-pair threshold lie below `nSquare`; the triple residual cutoff
does too. The axiom reports contain only `propext`, `Classical.choice`,
`Quot.sound`, and the single existing local `dirichlet_seven_eighths`.

`numerical_chen_from_lower` now leaves only the lower producer as a hypothesis.
Once a numerical `nLower` is proved, the endgame cutoff is

```
max(9, nLower, 3^(3^4000000000000), 3^(20000*10^40+1)).
```

All seven modules completing this branch passed the batch check with warnings
treated as errors. The full local import/axiom audit passed. No new external
dependencies, OpenAI imports, or local axioms were added.

## Logarithmic bounded-K and source-endpoint improvements

The active bounded-K coefficient no longer enumerates quotients up to an
exponential cutoff. With `A=C1*Kmax^7`, put

```
r = 6*(1+max(0,A))^(1/8)
f = exp(-8*r*log(6*r))
B = max(1,A)
R = 2*B*(1+2*Kmax).
```

`NumericalJointEnvelope.lean` proves `f <= E_D(s)` for every `D>=2`,
`log(D)<=A`, and `s>=2`. The large-s branch retains the perturbation factor:
once `s>=r`, it compensates for the coarse hat decay. For `A>=0`, the
same floor is at least `exp(-2000*(1+A)^(1/8)*log(e+A))`.

`NumericalLogarithmicScalar.lean` proves one coefficient `7*R^3*B^4/f`
for every natural quotient in that logarithmic range. The active
`boundedCaseAConstant` is this coefficient times `exp(sqrt(Kmax))`.
There is no quotient sum and no factor counting quotients. The older
fixed-quotient and finite-sum lemmas remain available for compatibility;
the assembly no longer uses them.

The compact derivative estimate now uses the floor
`1/(51200000000*m)`. Only the fixed head `[2,4]` uses an absolute hat
minimum. Beyond it, global comparison of the two hats and monotonicity
between adjacent arguments give the ratio bound directly. The derivative
cutoff consequently has a polynomial exponent in `m` at fixed `d`, rather
than the reciprocal of a rapidly decaying compact minimum.

For positive `d`, `sourceLowerCutoffFor d M` is now
`exp(max(e,max(1,M)^d))`. In the actual `d=16` source branch this replaces
`exp(exp(max(1,M)))`. The double-exponential compatibility branch is retained
only for `d=0`; it is not used by the Suzuki source assembly. Both improved
cutoffs feed the existing shared `numericalSuzukiC1` formula.

These changes reduce avoidable exponential layers in the constants. They
do not by themselves produce `nLower`. The base-candidate absorption and
normalization are completed below; the medium-prime upper estimate and final
Chen cutoff are also completed in the following closure.
The completed `nSquare` branch and its `10^40` triple error cap are unchanged.

## Completed numerical base-candidate lower bound

`NumericalBaseDensity.lean` proves the finite lower density at Chen's literal
floor level, uniformly in the adaptive supported-carrier depth. It consumes
the fully numerical Suzuki theorem directly, without selecting a constant,
an eventual threshold, or a continuity radius. The source-family index and
recursion depth are independent.

Let `Cnum=numericalChenSuzukiCoefficient`, `Knum=numericalLocalProductK`, and

```
c = ceil(max(1,Cnum)), k = ceil(max(1,Knum))
r = 20000000, epsilon = 1/(60*r) = 1/1200000000
DensityCutoff(r) = max(2, suzukiCoordinateThreshold,
                       suzukiErrorThreshold(c,k,r))
DistributionCutoff(m,d) = max(numericalBVThreshold(3),
  lowerDistributionThreshold(m,d,1000344400000012180))
nBase = max(DensityCutoff(2*r), sourceMassThreshold(r),
            DistributionCutoff(60*r,r)).
```

Here `c` and `k` are ceilings of closed numerical formulas; they are not
chosen witnesses. The existing definitions expand every threshold above
into integer arithmetic, powers, maxima, and the numerical Suzuki formulas.

For every even `N>=nBase`, `numerical_base_candidates` proves

```
(jurkatRichertBaseMainCoefficient(jurkatRichertJ)-1/40000)
  * S(N)*N/log(N)^2 <= card(jurkatRichertSourceCandidates(N)).
```

The proof uses `A=jurkatRichertBaseSieveFactor(J)`,
`B=jurkatRichertMertensFactor`, and `M=S(N)*N/log(N)^2`.
The explicit epsilon costs at most `1/(2*r)` in the lower factor, and
Suzuki absorption at `DensityCutoff(2*r)` costs less than `1/(2*r)`.
Thus the density factor is at least `A-1/r`. Source mass is at least
`(B-40/r)*M`, and the genuine finite Rosser remainder is at most `M/r`
by numerical BV. The proved elementary bounds `2/5<=A<=10` and `B<=20`
give total coefficient loss at most `421/r < 1/40000`.

`numerical_lower_from_medium_prime_bound` discharges the base hypothesis
of the finite weighted-lower endpoint. It needs only the actual medium-prime
aggregate upper bound with coefficient
`jurkatRichertQ1MainCoefficient(K)+1/20000`, above the maximum of `nBase`
and `lowerEndpointThreshold`. This input is now supplied by
`numerical_medium_prime_aggregate` below, completing the lower estimate.

The new proofs retain exactly the existing local `dirichlet_seven_eighths`
axiom, with zero OpenAI imports and no new dependencies.

## Completed medium-prime upper estimate and numerical Chen cutoff

`NumericalMediumAggregate.lean` proves, for every even `N` above the closed
`mediumPrimeAggregateThreshold`,

```
jurkatRichertSourceMediumPrimeAggregate N
  <= (jurkatRichertQ1MainCoefficient(jurkatRichertK)+1/20000)
       * S(N)*N/log(N)^2.
```

The constituent finite estimates are:

- `NumericalUniversalTail.lean`: if `z>=2*r`, the universal product truncation
  is at most `(1+1/r)` times the full product. A telescoping product over all
  integers bounds the omitted odd-prime tail. The genuine Liu singular-series
  correction then gives a uniform bound for every positive source integer.
- `NumericalSourceUpperMass.lean`: the common conditioned-sieve density is at
  most `(20*exp(-gamma)+300/r)*S(N)*N/log(N)^2`. The cutoff is
  `max(chenProductThreshold(r),(2*r+1)^10,3^(40*r+1),logPowerCutoff(2))`.
  Both the floored source cutoff and the literal logarithmic-integral
  normalization are paid numerically.
- `NumericalUpperFactor.lean`: the exponent profile
  `F(a)=jurkatRichertUpperLinearSieveFactor(5-10*a)` is bounded between `0`
  and `12` and has Lipschitz constant `180` on `[1/10,1/3]`.
- `NumericalMediumPrimeGrid.lean` and `NumericalMediumPrimeSum.lean`: an
  `n`-cell logarithmic grid gives weighted reciprocal-prime transfer error
  at most `196/n+192*n*18000000000000/log(N)`. With `n=10^12`, the already
  numerical prime-pair cutoff pays this by `10^-8`. The integral is exactly
  Chen's `2*exp(gamma)/5*(log(8)+K/2)`; no numerical integral assumption is
  introduced.
- `NumericalMediumPrimeShift.lean`: the shifted reciprocal-prime mass is at
  most `22`. At the positive epsilon below, the actual shifted weighted
  sum is at most the exact integral plus `10^-7`.
- `NumericalMediumUpperDensity.lean`: the literal upper Rosser density is
  bounded uniformly over all medium primes and their odd adaptive depths.
  The existing numerical Suzuki coefficient and the upper-window envelope
  bound give additive density error at most `1/r`.

The fixed upper budget and epsilon are

```
r = mediumPrimeBudget = 10^12
m = 120*r = 120000000000000
epsilon = 1/m.
```

With the same numerical integer Suzuki caps `c,k` as in the base proof, put

```
Q = max(152587890625,4096*(20*c*3^k+1)^2*r^2)
nUpperDensity = (3^Q+1)^10
nPrimeSum = max(primePairThreshold,(r+2)^10)
nMedium = max(nPrimeSum, sourceUpperMassThreshold(r), nUpperDensity,
              varyingNumericalThreshold(m,r)).
```

Every entry is a displayed numerical formula, not a selected witness. The
common density, weighted prime sum, uniform upper density, and numerical
weighted-BV remainder combine into a coefficient loss below `1/20000`.

The lower and final thresholds are now defined by

```
nLower = max(baseCandidateThreshold,nMedium,lowerEndpointThreshold)
N0 = max(9,nLower,3^(3^4000000000000),3^(20000*10^40+1)).
```

`numerical_weighted_lower` proves the actual coefficient `2.6407` for every
even `N>=nLower`. `NumericalChenCutoff.lean` then combines this with the
completed square/triple branch. For every even `N>=N0`, `numerical_chen`
proves `N=p+q`, with `p` prime and `q` prime or a product of two primes.
`numerical_chen_representation_count` also proves the quantitative lower
bound `0.67*S(N)*N/log(N)^2` for the actual good-representation count.

The final theorem has only the cutoff and parity hypotheses. Its axiom
report contains `propext`, `Classical.choice`, `Quot.sound`, and the single
existing local `dirichlet_seven_eighths`. There are zero OpenAI imports,
zero Li-Liu theorem imports, and no new external dependencies. This remains
a conditional result under that local Dirichlet axiom.

Validation: `check.ps1 -FromModule NumericalUniversalTail` compiled all nine
new modules with warnings treated as errors. The full import/local-axiom
audit passed, including the axiom reports for the final Chen and
representation-count theorems.

## Pure integer tower cutoff

`NumericalExplicitTower.lean` proves that both detailed thresholds are bounded by

```
T = 3^(3^(3^(3^(10^21))))
nLower <= T
N0 <= T.
```

Thus `numericalNLower = numericalN0 = T` is a concrete common choice.
`numerical_lower_above_tower` proves the weighted lower bound above this
integer, and `numerical_chen_above_tower` and `numerical_count_above_tower`
prove Chen's conclusion and the quantitative representation count above it.
The detailed cutoffs remain available and are smaller than this convenient cap.

The eight tower modules bound the source logarithmic cutoff, Suzuki C1,
bounded-K coefficient, integer Suzuki caps, BV and normalization cutoffs,
and final density absorption. The largest absorption cutoff fits within four
base-three exponential layers with top exponent `10^21`. This is a proved
conservative cap, rather than the earlier rough size estimate.

The threshold-comparison theorems use only Lean's standard axioms. The final
Chen theorem additionally uses the existing `dirichlet_seven_eighths` axiom;
no further axiom, OpenAI import, or external dependency is introduced.

Validation: `check.ps1 -FromModule NumericalTowerTools` checks all eight tower
modules with warnings treated as errors, then runs the full import and
local-axiom audit.
## Original theorem compatibility and final audit

`NumericalChenCompatibility.lean` derives `Goldbach.ChenTheorem`, the original
internal existential statement using `MathlibNt.ChensTheorem.Semiprime`, and
the original eventual `0.67` representation-count bound. All three proofs
use the numerical theorem at the concrete witness `numericalN0`. The bridge
imports only the independent public statement and almost-prime vocabulary,
not the old implicit Chen proofs.

The separate fixture `audit/AuditChen.lean` imports the old declarations only
to check definitional equality of the new and old statement types. It checks
all final numerical and compatibility theorems against the exact whitelist
`propext`, `Classical.choice`, `Quot.sound`, `dirichlet_seven_eighths`; the
threshold caps need only standard Lean axioms. It also traverses proof and
type dependencies to reject any use of the original implicit theorem proofs.
The traversal independently verifies the allowed axioms and rejects unsafe constants.
Thus importing the old statements in the audit cannot hide circular reasoning.

Run `./research/chen-effective/audit.ps1` for the compatibility and final audit,
or add `-Rebuild` to recompile all 148 research modules first. The source audit
covers all research modules and their locally imported project sources,
ignoring comments/string literals, and rejects proof placeholders,
`native_decide`, unsafe declarations, compiler bypass attributes/options, and every
axiom declaration except the one existing Dirichlet axiom. The transitive
axiom whitelist additionally checks proof dependencies in external libraries.
No external dependencies or OpenAI imports are introduced.

Final validation: all 148 research modules recompiled with warnings treated as
errors and unchanged source hashes. The source scan passed for 671 files; the
proof dependency walk passed for 81,818 constants. All four original statement
comparisons and all seven exact final-theorem axiom checks passed.

## Reproduce

From the checkout, in PowerShell:

```powershell
& ./research/chen-effective/check.ps1
```

After an interrupted check, `-FromModule ModuleName` resumes compilation at
that module; the full import and local-axiom audit still runs.

This checks only the 148 research modules, in dependency order, treating warnings as errors,
writes `.olean` files and axiom reports under `.lake/build/chen-effective/`,
and audits local imports and the single added axiom. It does not rebuild the
Li-Liu development or alter the pinned dependency manifests. `LEAN_PATH` is
temporarily extended with the research artifact directory and restored by the
script, and each source uses this directory as its package root. The ordinary
default `lake build` does not include these research files.
