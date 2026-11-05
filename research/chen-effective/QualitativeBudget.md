# Qualitative Chen: parameterized budgets and the remaining H=36 gap

The separate existence theorem uses `qualitativeN0 = 3^(3^2900)`.
In natural coordinates this is `exp(exp(H))` with
`H = 2900*log(3) + log(log(3))`, approximately 3186.070.
The existing 0.67 counting theorem retains its original cutoff and proof.

## Certified end-to-end allocation

Write `M = liuSingularSeries(N)*N/log(N)^2`.
`ChenBudget` separates the base, medium, endpoint, triple-main and
triple-remainder coefficients. Its generic theorems connect the actual
counting estimates to `R >= W - T/2` and prove existence whenever the
resulting margin is positive. `PrimeProductProfile` independently exposes
the pre-sieving endpoint and relative accuracy with their proof obligation.
The concrete allocation is `optimizedChenBudget`.

| Component | Proved qualitative allocation |
|---|---:|
| Relative prime-product error after pre-sieving | `10^-5` |
| Pre-sieving endpoint | `3^2788` |
| Principal-PNT and reciprocal-prime saving | `1/68` |
| Depth-uniform parity error multiplier | `4806` |
| Rounded-level ratio loss | at most `10^-7` |
| Lower-window factor `exp(2)*sieveHat(s)` | at most `1/16` |
| Base density error | `31/10000` |
| Medium density error | `49/1000` |
| Mertens normalization factor | at most `25/2` |
| Medium reciprocal-prime sum | at most `2` |
| Base-candidate coefficient loss | at most `1/25` |
| Medium-prime aggregate coefficient loss | at most `123/100` |
| Endpoint loss | at most `1/20000` |
| Final weighted count | at least `1.98575*M` |
| Triple main term | at most `3.94033*M` |
| Triple inverse-log remainder | at most `M/100` |

Thus the final normalized margin is
`1.98575 - 3.94033/2 - (1/100)/2 = 0.010585 > 0`.
The original public and internal implicit existence specifications follow
from this independent proof. The original implicit quantitative statement
continues to follow from the preserved 0.67 counting theorem.

## Improvements and limits

The principal smoothing balance is improved to power `1/68`, with all
contour terms checked against the same constant. Abel summation and the
actual Goldbach Euler product retain that saving. The product exponent is
now `1.3*10^14*u^(-1/68)`. At relative accuracy `10^-5`, pre-sieving below
`3^2788` suffices, compared with `3^5760` in the previous existence proof.
This is an improved analytic bound, without an assumed prime table.

The existing kernel recurrence is unchanged. Exact parity tail potentials
certify cap 4806 instead of 6000. Retaining the hat factor gives a much
smaller error on the lower-sieve window `s >= 9/2`. The upper aggregate
also uses the actual medium reciprocal-prime interval: its bound is 2
instead of 22. Together these improvements permit the larger product error
while preserving a positive final margin.

The Selberg divisor estimates now need a coarse Mertens product only from
`3^2176`, using the improved reciprocal-prime saving. The triple moment
and denominator arguments retain their previous form. Every producer is
instantiated at the stated common cutoff; no analytic estimate remains
an unproved hypothesis of the final theorem.

`budget_logarithmic_level_ratio` provides the exact ratio for
`D=N^(1/2)/(log N)^B`, including the pre-sieving cost. The concrete
weighted-distribution producer still uses its existing fixed power level.
A new logarithmic-level distribution theorem has not been substituted.
The parameters are reusable interfaces, not a certified global optimum.

## Why H=36 is not yet certified

1. **Small-endpoint prime products.** The power estimate still costs
   `log u = 2788*log(3)`, approximately 3063. Substantially sharper explicit
   products at small endpoints remain the leading obstacle.
2. **Selberg normalization.** The coarse absolute-moment error
   `10^24*(1+log(log N))^6/log N` is about `5.95*10^17` at H=36.
   Sharper normalized or signed moments, or a stronger sieve, are needed.
3. **Prime sums and distribution.** The existing prime-pair threshold
   includes `N >= 3^(10^80)`, giving H about 184.3 independently of the
   product estimate. Distribution constants and thresholds remain coarse.
4. **Triple remainder.** The retained cap is `C=10^40`. Allocating `M/100`
   is certified by `log N >= 200*C+1`, about H=97.4. Reaching H=36 requires
   reducing this coefficient or retaining a sharper decaying remainder.

The single local Dirichlet axiom is unchanged. No OpenAI modules, prime
tables, external estimates as axioms, or new dependencies are introduced.
