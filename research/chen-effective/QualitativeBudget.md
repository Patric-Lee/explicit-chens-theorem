# Qualitative Chen: numerical budget and the remaining H=36 gap

The separate existence theorem uses `qualitativeN0 = 3^(3^6000)`.
In natural coordinates this is `exp(exp(H))` with
`H = 6000*log(3) + log(log(3))`, approximately 6591.768.
The existing 0.67 counting theorem retains its original cutoff and proof.

## Certified positive margin

Write `M = liuSingularSeries(N)*N/log(N)^2`.

| Component | Proved qualitative allocation |
|---|---:|
| Relative prime-product error after pre-sieving | `10^-7` |
| Depth-uniform sieve-error multiplier | `6000` |
| Rounded-level ratio loss | at most `10^-7` |
| Each density error budget | `1/1000` |
| Base-candidate coefficient loss | at most `1/40` |
| Medium-prime aggregate coefficient loss | at most `1/2` |
| Final weighted count | at least `2.3*M` |
| Triple main term | at most `3.94033*M` |
| Triple inverse-log remainder | at most `M/2` |

The exact finite counting inequality is `R >= W - T/2`.
Consequently the remaining coefficient is

`2.3 - 3.94033/2 - (1/2)/2 = 0.079835 > 0`.

The proof conservatively bounds the actual representation count below by
`M/20` internally and uses positivity. No 0.67 theorem supplies this proof.
The public and internal original implicit existence specifications are
recovered from the qualitative theorem. The old implicit quantitative
specification continues to follow from the preserved counting theorem.

## What has changed quantitatively

The old lower branch required product accuracy `10^-20` and pre-sieved below
`3^10240`. The existence branch uses accuracy `10^-7` and the already proved
product estimate after pre-sieving below `3^5760`.

The old Selberg denominator used a Mertens-product theorem with threshold
`max(principalNumericalThreshold(1), 3^3600000000008)` at an endpoint
comparable to `log N`. The new coarse product theorem has endpoint `3^4096`.
It follows from the proved reciprocal-prime power error and the exact
logarithmic correction, so no external prime tables are assumed.

## Why H=36 is not yet certified

The following concern the strength of our current sufficient bounds. They
do not show that the actual arithmetic errors are large.

1. **Small-endpoint prime products.** The current interval estimate has
   exponent `1.3*10^14*u^(-1/128)`. Its present use at error `10^-7` costs a
   pre-sieving endpoint with `log u` about 6328. Sharper explicit product
   bounds at much smaller endpoints remain the dominant next ingredient.
2. **Selberg normalization.** The coarse absolute-moment bound is
   `10^24*(1+log(log N))^6/log N`. At H=36 its upper bound is about `5.95*10^17`,
   so it cannot certify even a modest denominator error there. Signed or
   sharper normalized moments, or a switched bilinear sieve, must replace
   this estimate for a paper-scale cutoff.
3. **Prime sums and distribution.** The current prime-pair threshold
   includes `N >= 3^(10^80)`; this alone has H about 184.3. This is an
   independent sufficient threshold that must be sharpened.
4. **Remainder coefficient.** We retain the conservative cap `C = 10^40`.
   Paying it by `M/2` requires `log N >= 4*C`, corresponding to H about 93.5.
   Further work must reduce the cap or retain a sharper decaying remainder.

The immediate optimization target is therefore accurate small-endpoint
prime-product control together with improved triple normalization and
explicit distribution constants. More accurate sieve recurrences can
increase the available error budgets, but do not by themselves remove these
independent analytic thresholds.
