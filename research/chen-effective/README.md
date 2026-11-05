# Effective Chen investigation

Status: the actual medium-prime aggregate upper estimate, the weighted lower
estimate, and the square/triple estimate are proved at closed numerical
cutoffs. **A closed numerical Chen threshold is now proved under the single
local Dirichlet seven-eighths axiom.** `NumericalChenCutoff.lean` supplies
`numerical_chen` and the quantitative representation-count theorem. There
are no remaining analytic estimates as hypotheses of these final theorems.
The active cutoffs are now `nLower = 3^(3^20000)` and
`N0 = nSquare = 3^(3^4000000000000)`. These are exact equalities,
proved in `NumericalMediumAggregate.lean` and `NumericalChenCutoff.lean`.
The earlier common cap in `NumericalDoubleExponential.lean` remains a valid coarse bound.
The threshold is an explicit formula built from the numerical constants
below; no unspecified or chosen analytic threshold occurs in it.

## Specialized sieve ingredients: power-saving product and coarse recurrence

`NumericalMertensPower.lean` preserves the principal PNT power saving through
Abel summation, proving, for every real `x >= 9`,
`|sum_{p <= x} 1/p - log(log x) - M| <= 3*10^13*x^(-1/128)`.
The constant is canonical and no eventual starting-point witness is used.

`NumericalEulerProductPower.lean` consequently proves, for real `10 <= u <= z`
and every subset of odd primes in `[u,z)`, the bound
`product <= (log z/log u)*exp(1.3*10^14*u^(-1/128))`.
After removing primes below `u0 = 3^5760`, its relative error is at most
`10^(-7)`, uniformly for **all** `1 < u <= z`, including `u < u0`.
It also specializes this bound to the literal source sifting product (shared
by the conditioned sieve) and proves the elementary cost `log Q <= (log 4)*u0`.
This uses the existing Dirichlet axiom and no external explicit-prime tables.

`NumericalSieveErrorRecurrence.lean` proves both parity sums of the coarse
specialized error recurrence are at most `6000` for `0 <= epsilon <= 1/200`.
The proof uses an exact remaining-error potential, so it is uniform in depth
and needs no finite recursion table. These scalar results use only standard
Lean axioms.

`NumericalSieveKernel.lean` now proves the analytic kernel bounds without
quadrature: `H(s) <= (241/250)*s*h(s)` for `s >= 2`, and
`H(3) <= (116/125)*s*h(s)` for `1 <= s <= 3`. A rational differential
supersolution proves the required exponential-integral estimate. Continuity,
monotonicity, and the global shift bound `h(s-1) <= 4*h(s)` are proved too.

`NumericalSieveLayerDecay.lean` proves the geometric hat bound for the actual
source-normalized continuous layers, including both closed parity endpoints.
`NumericalSieveRelativeAbel.lean` proves relative-product Abel estimates on the
actual finite prime atoms. `NumericalSieveSourceInduction.lean` then proves
domination of **every actual `suzukiSourceV` layer**, with exact natural-ceiling
cutoffs and recursive ceiling division. The compact odd range and the even
endpoint are included. `NumericalSieveKernelRecurrence.lean` and
`NumericalSieveSourceParity.lean` give the uniform error constant `6000` for
`0 <= epsilon <= 1/10000`, matched to these proved analytic bounds.

`NumericalPresievedSourceLayers.lean` instantiates that result at
`epsilon = 10^(-7)` for the restricted base and conditioned Chen prime
carriers. No kernel or layer estimate remains as an input to these two
instantiated theorems. The analytic layer proofs use only standard Lean
axioms; the Euler-product instantiations use the single local Dirichlet axiom.

Exact pre-sieving and the `QD` assembly are now proved in
`NumericalPreSieveCounting.lean` and `NumericalPreSieveRemainder.lean`.
The weights are the original weights times the exact indicator `(Q,n)=1`;
the mass is multiplied by the small-prime Euler factor. The sifted count
and mass times the full Euler product are unchanged. The remainder is the
literal Moebius sum `r_pre(d) = sum_{a|Q} mu(a)*r(ad)`.
Coprimality makes `(a,d) -> a*d` injective, so its total absolute remainder
is bounded by the original remainder below `QD`, with no multiplicity loss.

`NumericalPreSieveSharpProduct.lean` strengthens the relative product error
to `epsilon = 10^(-20)` by pre-sieving below `3^10240`.
`NumericalPreSieveDensity.lean` converts the actual parity-layer estimates
to both Rosser densities, with depth-uniform error `6000*epsilon`.
`NumericalPreSieveAssembly.lean` proves the resulting finite counting
inequalities. `NumericalPreSieveDistribution.lean` pays the **unweighted**
conditioned remainders using the same weighted BV constants and corrections;
it keeps all nonreduced lanes, including primes dividing `N`.

`NumericalPreSieveGeometry.lean` uses the level
`floor(X/(2*Q))+1`, proves `Q*D <= X` including rounding, and bounds the
sieve-ratio loss by `10^(-20)` above `3^(3^20000)`.
`NumericalPreSieveBase.lean` and `NumericalPreSieveAggregate.lean` recover
the original base and medium-prime coefficients and error budgets.
`NumericalPreSieveCutoff.lean` bounds every remaining mass, prime-sum,
distribution and endpoint threshold and proves the original `2.6407`
weighted lower bound. No Suzuki `C1` or source-cutoff budget enters this
new lower route. The final `0.67` representation count and the four original
Chen statement types are retained.

Thus the active lower cutoff has natural `log log` about `21972`, while the
final cutoff is dominated by the existing Selberg-square bound (natural
`log log` about `4.39445*10^12`). Reaching `H=36` still requires sharper
small-endpoint product bounds and improvement of the square denominator.
No literature table, new axiom, OpenAI module or dependency is added.

Validation: all 43 affected modules rebuilt with warnings treated as errors.
The extended audit recovered all four original Chen statement types, checked
the exact final-theorem axiom whitelist, and traversed 82,171 proof/type
dependencies. A separate traversal confirms that neither active final theorem
uses the obsolete C1 density estimates or their thresholds.

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

## Development history and proved results

The sections below record successive checkpoints. The final mixed-error closure supersedes the earlier outstanding-work descriptions and four-layer cap.

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
A = 10
E = 4*A + 52 = 92
Knum = (E+2)*3^(2*E) = 94*3^184 < 10^90.
```

`NumericalMertensGlobal.lean` proves the reciprocal-prime Mertens error is
at most `A/log(n)` for **every** integer `n >= 2`, using the elementary
Mertens proof described below. This replaces the former PNT-cutoff-based budget.
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

- Comparison `Qhat <= 51200 * T` and reverse-ratio cap
  `r = 51200 * (800 * 22^20 + 75)`.
- A forward majorant with `cMinus=1152`, `A=2`, cutoff `exp(2309)`.
- The sharp lower profile with coefficient `100` from `s=20000`,
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
`1/(51200*m)`. Only the fixed head `[2,4]` uses an absolute hat
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
T = 3^(3^(3^(3^(10^15))))
nLower <= T
N0 <= T.
```

This was the previous common choice. The public `numericalNLower` and `numericalN0` now use the double-exponential cap proved below.
`numerical_lower_above_tower` proves the weighted lower bound above this
integer, and `numerical_chen_above_tower` and `numerical_count_above_tower`
prove Chen's conclusion and the quantitative representation count above it.
The detailed cutoffs remain available and are smaller than this convenient cap.

The eight tower modules bound the source logarithmic cutoff, Suzuki C1,
bounded-K coefficient, integer Suzuki caps, BV and normalization cutoffs,
and final density absorption. The largest absorption cutoff fits within four
base-three exponential layers with top exponent `10^15`. This is a proved
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
or add `-Rebuild` to recompile all 150 research modules first. The source audit
covers all research modules and their locally imported project sources,
ignoring comments/string literals, and rejects proof placeholders,
`native_decide`, unsafe declarations, compiler bypass attributes/options, and every
axiom declaration except the one existing Dirichlet axiom. The transitive
axiom whitelist additionally checks proof dependencies in external libraries.
No external dependencies or OpenAI imports are introduced.

Validation before the elementary Mertens replacement: all 148 research modules recompiled with warnings treated as
errors and unchanged source hashes. The source scan passed for 671 files; the
proof dependency walk passed for 81,818 constants. All four original statement
comparisons and all seven exact final-theorem axiom checks passed.

## Elementary Mertens replacement

`NumericalElementaryMertens.lean` adapts only the elementary proof chain from
`PrimeNumberTheoremAnd/IEANTN/Mertens.lean` at upstream revision
`127b50e33f6033e2147921167a117af96d9ba4ea` (Apache-2.0). It imports Mathlib
modules only: no PNT+, IEANTN, Euler-Maclaurin, or numerical certificate module.
The source is https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/127b50e33f6033e2147921167a117af96d9ba4ea/PrimeNumberTheoremAnd/IEANTN/Mertens.lean.

The local port proves, for every real `x >= 2`,

```
|sum_{p <= x} 1/p - log(log x) - M| <= 10/log x.
```

Here `M` is explicitly defined by an integral of the bounded error in the first
Mertens theorem. Its numerical value is unnecessary: the existing interval
argument cancels any shared additive constant. `numerical_mertens_all` now
uses this elementary constant, with `globalMertensBudget = 10`. No identification
with the earlier PNT-based constant is assumed or required.

The boundedness witnesses used to prove integrability are themselves proved
with the explicit coefficient `log 4 + 4`. There is no implicit starting
threshold or unverified node statement in this proof chain. It uses Mathlib's
coarse Chebyshev bound, not the PNT+ `1.11*x` estimate whose finite verification
uses `native_decide`.

The existing local-product conversion now gives the certified literal cap

```
localProductExponent = 92
numericalLocalProductK = 94*3^184 < 10^90.
```

`audit/AuditElementaryMertens.lean` independently checks both elementary Mertens
endpoints: exactly `propext`, `Classical.choice`, and `Quot.sound`; no unsafe
proof dependencies, no Dirichlet axiom, and no imported project result. The
final Chen audit separately verifies that the elementary global Mertens and
local-product bounds need no Dirichlet axiom. The final Chen theorems retain
the original single Dirichlet axiom and the same statements.

The source-ratio/Suzuki C1 estimates are unchanged. This replaces one major
inflated input but does not yet certify a double-exponential final cutoff.
The previously proved four-layer tower cap remains valid.

Validation for this replacement: all 20 affected research modules rebuilt with
warnings treated as errors. The independent elementary audit traversed 43,607
proof dependencies; the complete final Chen audit traversed 81,977. The source
audit passed for 672 research/project files. Both proof-dependency audits
passed their exact axiom whitelists and unsafe-dependency checks. The old and
new Chen statements remain definitionally identical in the compatibility audit.

## Completed C1 improvements

The two avoidable hat losses are removed:

- `numerical_hat_compact_four` uses two half-steps on `[2,4]` and proves
  `T(sign,s) >= 1/12800` there. The global comparison is consequently
  `Qhat <= 51200*T`, replacing `51200000000*T`. The source-ratio coefficient
  falls from `102400000000` to `102400`, and the compact derivative floor
  improves to `1/(51200*m)`.
- Numerical logarithm bounds replace estimates of the form `log(x) <= x` in
  the sharp-profile constants. The barrier floor has log at least `-1000000`,
  and the resulting sharp-profile coefficient is `100`, replacing
  `60000000000`. `caseBSourceC1_eq` certifies `caseBSourceC1 = exp(100000)`.

Case II now uses `c1LogBudget(Dcut) = max(0,log(Dcut))` for conditions that
only require `D >= Dcut`. The proved conversion `le_of_c1LogBudget` recovers
every original level threshold from the large-log regime. Thresholds that
really bound C1 itself (the Case-B and gap constants) remain direct terms.
The original Case-II endpoint theorem and all of its consumers compile with
this smaller separator.

`NumericalC1SingleExponential.lean` proves the complete numerical separator bound

```
numericalSuzukiC1 <= exp(10^40).
```

This includes all Case-I, even, Case-II and Case-B constituents; it is not
merely a bound on one subcase. Its axiom report contains only `propext`,
`Classical.choice`, and `Quot.sound`. The final Chen theorem retains the
single local Dirichlet axiom and its original existence/count statements.

The previous tower cap also tightens to `3^(3^(3^(3^(10^15))))`. The smaller
single-exponential C1 does not yet establish a double-exponential N0: the
uniform bounded-K coefficient and its final absorption remain to be tightened.

Validation: all 55 affected existing research modules and the new C1 cap module
compiled with warnings treated as errors. The statement, exact-axiom and
unsafe-dependency audits passed, including the independent traversal of
81,989 final proof dependencies. The source audit passed for 673 research/project
files. The elementary Mertens audit still passes.
No external dependencies or OpenAI imports were added.
## Absolute small-quotient errors: verified local estimates

`NumericalSmallQuotient.lean` bounds the entire actual finite parity sum by
`exp(suzukiSourceL(p,K))`, using the sum of the factorial majorants directly.
For every depth and `2 <= p <= q` with `log(q) <= A`, this proves

```
suzukiActualT S n q p <= R(A,K),
R(A,K) = 2 * max(1,A) * (1+2*K).
```

No real-coordinate restriction or hat minimum enters this bound. The module
splits the actual recursive prime sum at the natural quotient `ceil(D/p)`.
Large quotients retain their induction estimates; the immediate small-quotient
contribution is at most `R(A,K) * log(R(A+1,K))`. The supported-prime mass is
estimated using the existing local product bound, without counting primes or
quotients. For primes with `p^2 <= D`, the immediate small carrier is empty
when `log(D) > 2*A`; this does not exclude terminals at later depths.

`NumericalSmallQuotientChen.lean` specializes these statements to the literal
Chen source family and `A = numericalSuzukiC1 * numericalLocalProductK^7`.
The single terminal coefficient is bounded by `exp(10^42)`, and the entire
immediate terminal sum is bounded by `exp(10^43)`. Both are kernel-verified
single-exponential bounds with only the three standard axioms.

At this intermediate checkpoint these local estimates did **not** replace `fixedSuzukiCoefficient` in the
all-depth induction. What remains is a depth-uniform bound on the propagated
terminal error, including the odd low strip and Case-II recursion. Bounding
one terminal sum does not establish that bound: simply paying the same error
at every depth would lose uniformity. After that theorem, propagate the new
error through the base lower and medium-prime bounds and final absorption.
The certified `nLower`, `N0`, and four-layer tower cap are unchanged here.

The new modules are part of the research build and the standard-axiom and
unsafe-dependency audit. No dependency or OpenAI import is added.

Validation: both new modules and the extended audit compile with warnings
treated as errors. The source audit passes for 675 research/project files;
the proof dependency traversal passes for 82,017 constants. The original
statement comparisons, exact final four-axiom whitelist, and elementary
Mertens audit still pass. The new local bounds use only the standard axioms.

## Polynomial correction: verified transport and bounded branch

Eight `NumericalPolynomial*.lean` modules replace the flat local error by a
profile that retains decay in the internal coordinate. They prove:

- `x^4 * suzukiActualT S n q p <= 256 * R(A,K)^17`, uniformly in depth `n`,
  for `x >= 2`, `p = ceil(q^(1/x))`, and `log q <= A`. The factorial estimate
  sums a weighted tail; no compact hat minimum is used.
- The unperturbed correction is `P(D,s) = (log D)^(-5/8)/s^4`. For actual
  natural ceiling quotients, its normalized inherited prime sum is at most
  `(11/12)*P(D,s)` when `s >= 16`. This includes the discrete local-product
  endpoint error, under the numerical gate `288*K^2 <= log w`.
- On the cubic Case-II carrier, the actual inherited sum is at most
  `(log D)^(-5/8)/(10*s)`. This is a depth-independent transfer bound, not a
  contraction on the odd low strip. The proofs retain the actual ceiling
  quotient and Euler-product suffix ratios.
- On the compact Case-I strip the coarse kernel costs at most `3/8`.
  With `b = exp(-20000)`, the correction can be charged to `1/(100*sigma)`
  of the hat budget on `[2,16]`, using the fixed floor `exp(-12288)`.
- The gates are numerical: `log D >= logPowerCutoff 32` implies
  `sigma(D)*(log D)^(-1/8) <= 1`. With `K >= 2` and `K^7 <= log D`, it also
  implies `288*K^2 <= log(D^(1/sigma(D)))`. No eventual threshold is selected.
- The bounded-level mixed Claim-14.5 scale has a polynomial coefficient
  `1792*R(A,K)^18*max(1,A)^4/b`. For the current Chen separator and local
  product constant, that coefficient is bounded by `exp(10^45)`.

The mixed scale is the old Claim-14.5 scale plus `b` times the polynomial
correction scale. The new term is **not** multiplied by the old perturbation
factor, which would invalidate the polynomial tail integral.

At this intermediate checkpoint the full mixed-error induction was unfinished. The
Case-I strict and even-endpoint producers and the Case-II final assembly must
be rethreaded with this invariant and the compact-strip payment, preserving
enough of their contraction gap. Per-step depth-independent estimates do not
alone prove a bound on the accumulated stopping tree. Only after that proof
can the base and medium-prime densities use the single-exponential coefficient.
The certified `nLower`, `N0`, and four-layer tower cap are unchanged here.

All eight modules are included in the research build and in the standard-axiom
and unsafe-dependency audit. No new dependency or OpenAI import is added.

Validation: all eight modules compile with warnings treated as errors. The
source audit passes for 683 research/project files, and the extended proof
dependency traversal passes for 82,075 constants. The new polynomial bounds
use only the three standard axioms. The original statement comparisons,
final exact four-axiom whitelist, and elementary Mertens audit still pass.

## Completed mixed-error induction and double-exponential cutoff

`NumericalMixedInduction.lean` now proves `numerical_mixed_suzuki` for every
positive recursion depth, including natural-ceiling quotients. Its invariant
uses the original hat envelope plus

```
exp(-20000) * (log D)^(-5/8) / s^4.
```

The bounded-level branch uses the polynomial terminal coefficient. Large
levels retain a contraction of `1 - 1/(10*sigma)` in Case I, including the
compact strip, the closed odd cubic endpoint, and the even endpoint. Case II
uses the exact cubic-cutoff identity and the contracted Case-I estimate at
the same depth and `s = 3`; that estimate uses the predecessor-depth induction
hypothesis, so this step is not circular. The scalar Case-II closure pays its
local-product and source errors from the retained contraction gap. No error
is multiplied by the recursion depth.

`NumericalMixedWindow.lean` converts this invariant to twice the old hat-error
shape on Chen's actual coordinate window `3/2 <= s <= 5`. Both the base lower
density and the medium-prime aggregate upper density now use this theorem.
`NumericalMixedCoefficientCap.lean` proves the effective coefficient is at
most `exp(10^47)`. Analytic induction modules are separated from the later
numerical cap certificates to keep the import graph acyclic.

`NumericalDoubleExponential.lean` proves the literal integer bounds

```
nLower <= 3^(3^(10^100))
N0     <= 3^(3^(10^100)).
```

These are kernel-verified conservative caps, not size estimates. Existing
BV, source-mass, normalization, square/triple, and final-error bounds fit
inside this same cap. `numericalNLower` and `numericalN0` now equal this
integer; their older `_above_tower` entry points remain available with the
improved constants. The new `numerical_chen_above_double_exp` and
`numerical_count_above_double_exp` give the literal Chen conclusion and the
same `0.67` representation-count bound. The lower coefficient remains
`2.6407`, the triple coefficient `3.94033`, and the triple error cap `10^40`.

The full induction, coefficient cap, and cutoff comparisons use only Lean's
three standard axioms. The final Chen results retain the single local
Dirichlet seven-eighths axiom. No OpenAI module or dependency is added.

Validation: all 32 affected modules compiled in dependency order with warnings
treated as errors. The installed checkout passed the source audit for 698
research/project files and the proof traversal of 81,907 constants. The
elementary Mertens audit passed independently. All four original statement
comparisons and all nine exact final-theorem axiom checks passed, including
the double-exponential entry points. The audit also checks that the numerical
proofs do not use the original implicit Chen proofs.

## First quantitative tightening of the double-exponential cutoff

The current common cap is `3^(3^(10^43))`, replacing the preceding
`3^(3^(10^100))` certificate. In natural logarithmic coordinates this is
`log log N` approximately `1.099 * 10^43`. This remains a conservative cap;
it does not claim proximity to `exp(exp(36))`.

- `NumericalSqrtAbsorption.lean` bounds `exp(sqrt K)` by
  `3^(Nat.sqrt k+1)` when `K <= k`, preserving the square root in both the
  lower-density and medium-prime upper-density absorption thresholds.
- `NumericalProductExponential.lean` retains the exponential Euler-product
  estimate before linearization. `NumericalProductSplit.lean` splits at 1024.
  Below 1024, a product over all integers telescopes, avoiding a large finite
  prime computation. Above 1024, the exponential estimate has a fixed small
  exponent. The resulting interval bound holds at every real lower endpoint
  `z >= 2`, including the closed endpoint. It proves a global local-product
  constant `K = 10^12`, replacing `94*3^184` in the active Chen proof.
- The compact hat proof now uses `log(6*s) <= 7` on `[2,16]`, giving the
  floor `exp(-896)` instead of `exp(-12288)`. The polynomial correction
  weight increases from `exp(-20000)` to `exp(-1000)`. The full mixed
  induction, including compact Case I, the even endpoint and Case II,
  is rebuilt with this stronger correction.
- `NumericalSuzukiSharpBudget.lean` tracks the powers in the terminal
  coefficient directly. For the refined local product constant it proves
  an effective Suzuki coefficient at most `exp(10^42)`, replacing the
  previous `exp(10^47)` cap. `NumericalDoubleExponential.lean` propagates
  these bounds to both detailed thresholds and the public convenience cutoffs.

The remaining major lower-sieve losses include the global C1 separator,
derivative-ratio bounds, large-level gate, and deliberately small error
allocations. Independently, reducing the full cutoff toward `exp(exp(36))`
also requires tightening the square/denominator threshold, the final triple
error constant, and distribution thresholds. The original `0.67` count
coefficient and the single local Dirichlet axiom are retained. No OpenAI
module or external dependency is added; the sieve structure is unchanged.

Validation: all 40 affected modules compiled in dependency order with warnings
treated as errors. The extended audit traversed 81,946 proof/type dependencies,
checked all four original statement comparisons and all nine final-theorem
axiom whitelists, and verified that every new product, absorption, compact-hat,
and coefficient lemma uses only the three standard axioms. The final source
and elementary Mertens audits also pass.

## Relative hat bounds and the smaller C1 budget

`NumericalRelativeHat.lean` obtains neighbouring-value bounds from the positive
tail identity and monotonicity, rather than an absolute minimum on `[3,10]`.
Two half-steps give a factor 484 for the weighted hat on `[4,10]`, and a
factor 968 for the sum of the two hats. On `[3,4]`, the existing short-interval
floor completes the initial ratio estimate. The resulting initial ratio is
at most 10000, and the reverse slope is 10065.

The global reverse-ratio constant decreases from approximately `2.89*10^34`
to `515840000`. The first-crossing proof propagates the improved seed to the
entire tail. All later source-ratio and derivative certificates are rebuilt.
The separator is now bounded by `exp(10^16)`, and the effective coefficient
by `exp(10^18)`. Both `nLower` and `N0` are bounded by
`3^(3^(10^19))`, or natural `log log N` approximately `1.099*10^19`.

All 72 affected modules compile with warnings treated as errors. This
checkpoint completes the relative-hat improvement; separating the hat and
polynomial coefficients is the next step. The original count coefficient,
single local axiom, import restrictions and dependency boundary are retained.

## Independent hat and polynomial error coefficients

`NumericalSeparateCoefficients.lean` proves an all-depth natural-ceiling bound
with error

```
exp(sqrt K) * (C * errorEnvelope * (log D)^(-1/2)
                + P * (log D)^(-5/8)/s^4).
```

The two coefficients satisfy explicit compatibility conditions:
`C >= 36`, `C >= 4*lowStripNumericalConstant C1`, and
`4*max(1,polynomialTerminalConstant(C1*K^7,K)) <= P <= C`.
There is no fixed lower bound on `P/C`. A concrete unequal allocation is
also proved with these conditions discharged. The underlying induction is
generic in the ratio `P/C`, covering compact Case I, the even endpoint and
Case II. These are theorem hypotheses for a selectable error budget, not
new axioms; the final Chen proof uses a fully specified profile.

The active correction weight is now exactly 1. Consequently, the bounded
branch's coefficient is the terminal coefficient itself, with no division
by `exp(-1000)`. `unweighted_mixed_claim_coefficient` certifies this exact
formula. The common hat/poly budget remains available as one allocation.

The stronger estimate `sigma(D)*(log D)^(-1/8) <= exp(-940)` retains the
logarithmic decay that the earlier compact payment discarded. It makes the
unweighted correction affordable against the `exp(-896)` compact hat floor.
The final window conversion now requires the explicit logarithmic gate;
that gate is included in the lower and medium-prime scalar thresholds and
discharged in both actual Chen applications. It is not an additional
analytic assumption of the final theorem.

The common certified cap remains `3^(3^(10^19))`: the C1/source-cutoff budgets
still dominate it. This checkpoint removes the fixed exponential penalty
from the coefficient formulas and provides independent coefficient control
for future refinements, without claiming a further reduction of the common
cap. The single Dirichlet axiom, original Chen statements and count coefficient
are retained; no OpenAI module or external dependency is added.

Validation: all 40 affected modules compile with warnings treated as errors.
The extended proof/type traversal checks 81,976 constants, including the
generic coefficient theorem, its concrete unequal allocation, the exact
unweighted coefficient formula, and both numerical gate lemmas. They use only
the standard axioms. All four original statement comparisons and all nine
exact final-theorem axiom checks pass. The installed source scan and the
independent elementary Mertens audit also pass.

## Reproduce

From the checkout, in PowerShell:

```powershell
& ./research/chen-effective/check.ps1
```

After an interrupted check, `-FromModule ModuleName` resumes compilation at
that module; the full import and local-axiom audit still runs.

This checks only the 210 research modules, in dependency order, treating warnings as errors,
writes `.olean` files and axiom reports under `.lake/build/chen-effective/`,
and audits local imports and the single added axiom. It does not rebuild the
Li-Liu development or alter the pinned dependency manifests. `LEAN_PATH` is
temporarily extended with the research artifact directory and restored by the
script, and each source uses this directory as its package root. The ordinary
default `lake build` does not include these research files.
