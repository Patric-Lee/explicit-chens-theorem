# Complete upper-count remainder and the remaining product obligation

## Verified upper count

`ChenEffective.H30.fifth_triple_closed` proves, for every even
`N >= 3^(5*10^12)` and `K >= 8.2`,

\[
 T(N)\le \bigl(K(0.49254+10^{-4})+10^{-3}\bigr)
              \mathfrak S(N)N/(\log N)^2.
\]

The exact natural-number cutoff has
`H = log(5*10^12) + log(log 3)`, approximately 29.334507.
This is an actual corrected triple-count bound, not a scalar allocation
or a conditional assumption about the square remainder.

The proof retains two different decay orders:

\[
 T(N)\le K(0.49254+10^{-4})M(N)
       +C_5N/(\log N)^5+19N/(\log N)^3,
 \qquad C_5+19\le10^{34}.
\]

The last 19 includes the proved paper-Q residual (6) and the complementary
corrected triples (13). The square uses the actual optimal Selberg weights,
the proved denominator expansion, the logarithmic-integral prime-pair main
sum and the actual Pan remainder with saving A=5. All A=5 analytic thresholds
are proved to fit the same `3^(5*10^12)` cutoff.

For `L=log N >= 5*10^12` and `S(N)>=1/2`, the proof pays

\[
 C_5/L^3\le1/4000,\qquad19/L\le1/4000,
\]

so their combined contribution is at most `0.001 M(N)`.
This avoids charging `10^40/log N` to the budget: no improvement of that
older third-order constant is needed.

With `K=8.2`, a lower bound `W(N)>=2.02575 M(N)` gives

\[
 W(N)-T(N)/2\ge0.005426 M(N)>0.
\]

`chen_of_lower` proves the representation statement from exactly that lower
count at this cutoff. It does not prove that the lower count holds here.

## Product estimate: still open

`BJSH30SmallEndpoint.lean` proves the following reduction, including the
closed-left prime endpoint and Goldbach local-factor corrections. If

\[
 \left|\sum_{p\le x}\frac1p-\log\log x-B_1\right|
       \le1/20000\qquad(4\cdot10^6\le x\le3^{120}),
\]

then, for `4*10^6 <= u <= z` and every finite set of odd primes in `[u,z)`,

\[
 \prod_{p\in s}(1-1/(p-1))^{-1}
      \le(1+1/4000)\,\log z/\log u.
\]

Here `B_1` is the existing `mertensSecondConstant`. The infinite range
`x>=3^120` is already discharged by the proved Dusart branch. Thus only
the displayed bounded analytic range remains in this reduction. It is
enormous; this is not a claim that exhaustive computation is practical.

`SmallEndpointPrefixWindow` names this remaining proposition. It has no
proof or axiom declaration, and is an explicit hypothesis of the product
adapter. Kernel-checking that adapter does not establish the proposition.
The complete Chen theorem remains at `3^(3^134)`, H approximately 147.308095.
The near-30 lower-count mass/distribution/medium-sum assembly also remains
to be connected after obtaining a suitable product profile.

## External-source review

No external source was imported or vendored in this change, and no Lake
dependency changed. The following public sources were inspected:

* PNT+, main `127b50e33f6033e2147921167a117af96d9ba4ea`:
  [Dusart.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/127b50e33f6033e2147921167a117af96d9ba4ea/PrimeNumberTheoremAnd/IEANTN/Dusart.lean)
  has `sorry` in the relevant small-endpoint Mertens/product estimates,
  including Theorem 5.9. Those statements were not used as proved inputs.
* IEANTN, main `d60421f10c16f5f6c2cb75f1067a72e24e616391`:
  [Dusart2018 conclusions](https://github.com/teorth/IEANTN/blob/d60421f10c16f5f6c2cb75f1067a72e24e616391/IEANTN/Nodes/Dusart2018/v1/Conclusions.lean)
  explicitly describe a literature stub. The
  [RosserSchoenfeld.v2 conclusion](https://github.com/teorth/IEANTN/blob/d60421f10c16f5f6c2cb75f1067a72e24e616391/IEANTN/Nodes/RosserSchoenfeld/v2/Conclusions.lean)
  requires finite RH up to height 1894438.5122. Its solution transports
  that hypothesis; it does not prove that full-height verification.

## Validation

All five new Lean modules compile with warnings treated as errors.
`AuditBJSH30Triple.lean` traverses `chen_of_lower`'s dependency closure,
requires the actual square/prime-pair/Q/complement producers, rejects
unsafe constants and unlisted axioms, and excludes the older complete
triple/final Chen routes. The only nonstandard axiom remains
`ChenEffective.dirichlet_seven_eighths`. The product reduction's axiom
ledger is checked separately, and its unproved hypothesis is stated above.
