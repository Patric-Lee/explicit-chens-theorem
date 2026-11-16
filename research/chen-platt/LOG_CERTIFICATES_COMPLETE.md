# Completed logarithm certificates

The `Log256` campaign has 937 checked chunks containing 239,866 grid points
from 4,000,000 through 10,000,000,000. `LOG_CERTIFICATES_VERIFIED.json` records
the current receipt, source, object, configuration, dependency and coordinate
checks. This is a reproducible artifact check, not a new Lean computation or
the final Chen audit.

Recheck without regenerating or recompiling any chunks:

```powershell
node research/chen-platt/tools/VerifyCompletedPlattLogs.mjs .
```

An optional second argument writes a JSON report. Run from the repository root,
with Node on PATH (or use its full executable path). The verifier reads the
counting campaign's grid input but never changes the counting ledger or chunks.

For each certified row with integer endpoints `lower`, `upper` and scale
`S = 2^48`, the existing soundness proof gives

\[
\frac{\mathrm{lower}}S\le\log\log x\le\frac{\mathrm{upper}}S.
\]

`PlattLogGridBridge.lean` connects those bounds to `relative_cell_paid`. Given
certified rows at cell endpoints `a,b` and reference `r`, and prime-sum bounds

\[
L\le P(a)-P(r),\qquad P(b)-P(r)\le U,
\]

it pays the interpolation budget whenever

\[
-\delta\le L-\frac{b.\mathrm{upper}}S+\frac{r.\mathrm{lower}}S,
\qquad
U-\frac{a.\mathrm{lower}}S+\frac{r.\mathrm{upper}}S\le\delta.
\]

Here `P(x)` is the sum of reciprocals of primes at most `x`, and
`delta = finiteAllowance`. The conclusion holds for every real `x` in `[a,b]`,
including primes and noninteger points. The theorem does not assume that the
prime-sum bounds have already been proved.

Remaining work includes kernel-level full grid coverage and seams, completed
prime counts and reciprocal-sum assembly, the missing analytic source estimates
for the proposed 2e9 endpoint, and the final H30 axiom replacement/audit.
The production finite counting endpoint is still 1e10.
