# Preserved conditional low-cutoff study

Annotated tag: `study/bjs-low-cutoff-conditional-927c1eb8`

Commit: `927c1eb8`

That snapshot contains the complete earlier BJS proof development, numerical
budgets, certified sieve tables, reciprocal-prefix results, and theta and
H=36 studies. Its Chen theorem had cutoff `3^(3^171)` (H approximately
187.956749), conditional on Dirichlet AND `bjsStudy_interval`. It was not
a Dirichlet-only result. Both density assumptions had already been proved.

Inspect any old file without changing the working tree, for example:

```powershell
git show study/bjs-low-cutoff-conditional-927c1eb8:research/chen-bjs-study/README.md
git show study/bjs-low-cutoff-conditional-927c1eb8:research/chen-bjs-study/BJSStudyProducts.lean
```

The remaining low-endpoint analytic goal was the prime-product profile from
U=3^120. `BJSMertensThetaTarget` proved a sufficient conditional route through
`|theta(t)-t| <= (3/4)*t^(15/16)` above that endpoint, including its exact
composite left endpoint; that theta hypothesis was not proved. Signed prefix
estimates were proved for the lower finite range through 286 and both signs
from 3^3072, leaving the intervening analytic range open.

Those useful study modules are retained in the current package. Its active
Chen theorem instead uses a larger, fully proved product cutoff. The old
interval axiom is preserved only in Git history, not as an active declaration.
