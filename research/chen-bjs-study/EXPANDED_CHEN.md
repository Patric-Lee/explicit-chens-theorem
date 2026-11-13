# Propagation of the Selberg expansion to Chen existence

`BJSExpandedChen.lean` uses the new two-term expansion through the actual
denominator, optimized Selberg weights, square count, corrected triple
penalty, and final counting argument. It also proves the original literal
`Goldbach.ChenTheorem` statement. Neither earlier final Chen proof is used.

## Numerical results

| Component | Proved bound or parameter |
| --- | --- |
| Denominator threshold | `expandedSelbergThreshold = 3^1000000` |
| Denominator conclusion | `G_N(R) >= log(N)/(K*S(N))` for every `K >= 8.1` |
| Final existence cutoff | `expandedChenN0 = 3^(3^171)` |
| Chosen K | `expandedChenK = 8.2257261896036` |
| Charged normalized triple remainder | `expandedChenRemainder = 10^-40` |
| Positive Chen margin | `0.00000000000001194782 - 1/(2*10^40)` |

The denominator conclusion uses the actual source radius
`R = floor(N^(1/4-squareEpsilon/2))`, with `squareEpsilon=10^-10`.
Its threshold is approximately exp(exp(13.90956)); the old relaxed denominator
threshold was 3^(3^83), approximately exp(exp(91.27887)).

The final cutoff remains exp(exp(187.956749...)). The lower-count geometry
producer still requires 3^(3^171), independently of the denominator. This
propagation removes the previous denominator route from the new proof, but
does not replace the lower-count geometry or existing distribution and
square-remainder producers with smaller-cutoff versions.

## How the expansion is paid

The elementary prime-divisor estimate proves

\[
\mathfrak S(N)\le
\exp\!\left(822+\frac{3\log N}{64}\right).
\]

Combining this with the expansion error and the floor-radius bound gives

\[
\mathfrak S(N)\frac{20e^{1096+(\log N)/16}}{\sqrt R}\le1
\qquad (\log N\ge10^6).
\]

The positive secondary term can then be retained or discarded. Even
discarding it proves the denominator bound with K=8.1; monotonicity supplies
every larger K. This component uses only standard Lean axioms and no
small-endpoint Mertens estimate.

The actual square and triple remainders still have their proved cap 10^40.
At the final cutoff, S(N)>=1/2 and log(N)>=3^171 imply

\[
10^{40}\frac{N}{\log^3 N}
\le10^{-40}\mathfrak S(N)\frac{N}{\log^2 N}.
\]

This is a smaller allocation for the same proved error, not a new claim
that its analytic constant has improved.

## Interchangeable optimal budget

`expanded_chen_from_budget` is proved for every real K satisfying

\[
K\ge8.1,\qquad
K(0.49254+10^{-7})+10^{-40}<4.0515.
\]

Thus the admissible upper endpoint is

\[
K_* = \frac{4.0515-10^{-40}}{0.4925401}
\approx8.225726189603648515.
\]

The endpoint is strict, so there is no largest admissible K.
`expanded_chen_K_near_boundary` proves that the displayed choice is below
K_* by less than 5*10^-14. The complete family remains available: a choice
such as 8.2 gives a larger margin if later producers need more room.

## Verification

`AuditBJSExpandedChen.lean` checks the numerical thresholds and traverses the
proof recovering the original statement. It requires the new two-term
expansion to occur in that proof's dependency closure, excludes both old
final Chen proofs, and permits exactly the existing local Dirichlet axiom
plus Lean's standard axioms. The denominator and scalar budget components
are audited separately as using only standard axioms.

Run `check.ps1 -FromModule BJSExpandedDenominator` after the Selberg expansion
prerequisites have been built. No new dependencies or OpenAI imports are
introduced.
