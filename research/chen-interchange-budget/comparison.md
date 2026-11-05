# Interchangeable Chen budget: target comparison

Numerical exploration only. Positive local margins below assume the listed product and analytic inputs. No new cutoff is certified by this report.

| H | Product / sieve | Local margin before triple remainder | Maximum allowed extra triple coefficient | Current triple remainder formula |
|---:|---|---:|---:|---:|
| 29 | U=10^6 / verified 4806 | 0.151319 | 0.302637 | 5.0873313E+27 |
| 29 | U=1500 / assumed BJS 110 | 0.077602 | 0.155203 | 5.0873313E+27 |
| 25 | U=10^6 / verified 4806 | 0.092013 | 0.184025 | 2.7775888E+29 |
| 25 | U=1500 / assumed BJS 110 | 0.077513 | 0.155025 | 2.7775888E+29 |
| 20 | U=10^6 / verified 4806 | -8.813596 | -17.627192 | 4.1223072E+31 |
| 20 | U=1500 / assumed BJS 110 | 0.064151 | 0.128302 | 4.1223072E+31 |
| 15 | U=10^6 / verified 4806 | outside sieve window | unavailable | 6.1180464E+33 |
| 15 | U=1500 / assumed BJS 110 | -1.918871 | -3.837741 | 6.1180464E+33 |

These formulas are evaluated outside several known validity ranges. The JSON ledger retains those unpaid cutoffs; the displayed values are not asserted as bounds on the actual counts at these targets.

The local margin includes base, medium, mass/remainder allocations, level rounding, the endpoint allocation and half of the current triple main coefficient 3.94033. The current inverse-log triple remainder is still enormous at these targets; it is never replaced by the 0.01 allocation paid at the much larger proved cutoff.

The U=10^6 profile needs an unproved all-interval asymmetric prime-product estimate and endpoint bridges. The U=1500 profile additionally needs a port of the external prime-square certificate and uses the two existing temporary BJS density assumptions. Neither profile supplies mass/distribution estimates at these H values.

Research slots for improved Selberg moments and a switched bilinear triple estimate are present in catalog.json. Missing formulas remain unavailable. The switched route also needs a proved counting-model and normalization adapter.

Known Lean certificates remain 3^(3^2900) with Dirichlet only and 3^(3^171) with the three existing temporary BJS assumptions. They are reproduced by the new route adapters, independently of their old final Chen proofs.
