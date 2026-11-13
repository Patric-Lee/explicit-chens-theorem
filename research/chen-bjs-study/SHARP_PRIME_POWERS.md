# Sharper prime-power correction

The elementary theorem `ChenEffective.HybridProduct.prime_power_gap_two`
proves, using standard Lean axioms only,

\[
0\le\psi(x)-\theta(x)\le2\sqrt{x}\qquad(x\ge3^{16}).
\]

It bootstraps the existing global 17*sqrt(x) bound at the smaller roots via
Mathlib's Costa–Pereira inequality. No OpenAI result, numerical certificate,
new axiom, or dependency is needed for this improvement.

`BJSHybridSharpPrimePowerIntegral.lean` propagates it to the actual integral:

\[
\left|\int_a^b(\psi(t)-\theta(t))q(t)\,dt\right|
\le4(1/\log a+1/\log^2a)a^{-1/2},\qquad a\ge3^{16},
\]

where q(t)=(log(t)+1)/(t log(t))^2. This replaces the earlier coefficient 34.
`BJSHybridSharpAnalyticBridge.lean` also replaces the endpoint coefficient
17 by 2. Its finite-head hypotheses remain explicit. Its transitive audit
now permits only standard Lean axioms; the Dirichlet input is proved by
the vendored OpenAI development. The previous 69,665 count predates that integration. The elementary prime-power and integral bounds use standard axioms
only. Neither the reciprocal-window axiom nor numerical zero data is used
to prove the analytic bridge.

## Smaller certificate candidate at the same H

The existing product profile U=4,000,000 and epsilon=1/4000 is unchanged.
The existing prefix allowance 1/9000 is unchanged. Consequently the Chen
cutoff remains exactly 3^(10^13), H approximately 30.02765403654.

The new numerical candidate uses:

- 400,000 positive zero candidates, last ordinate 260876.634035043;
- derivative mass A<=18;
- positive head moment >=0.0461772 and total moment <=0.046192;
- omitted-zero moment W<=0.0000222;
- prime sums and logarithm grid through X=10^10.

The actual sharper bridge's numerical envelope at X is approximately
0.000108926119, below 1/9000. The regenerated finite grid has 31,304
endpoints and 455,052,511 primes; its integer/logarithm consistency checks
pass. A 10,001-point sampling checks numerical decrease of the tail envelope.

These are numerical feasibility checks, not completed Lean certificates.
Actual zero boxes, the full prime/log grid, the B1 enclosure, and the uniform
scalar payment still need kernel certification. The new candidate halves
the prime range and reduces the positive zero count by 20%.

See `hybrid-pilot/CheckSharpHybridInput.mjs`,
`hybrid-pilot/ValidateSharpHybridPilot.mjs`, and
`hybrid-pilot/sharp-hybrid-numerical-check.json`.

## Proved Dirichlet integration

The complete pinned OpenAI proof and the final Chen dependency closure have
compiled and passed their transitive audits on Lean 4.34.1 and the exact
upstream Mathlib revision. The former Dirichlet axiom is deleted.
The sharp hybrid bridge uses standard Lean axioms only. The numerical
prime/zero certificates described above remain separate outstanding work.
See [the final integration report](../chen-effective/UPGRADE_434_AUDIT.md).
