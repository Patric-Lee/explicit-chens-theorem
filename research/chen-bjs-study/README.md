# Numerical Chen with proved BJS sieve and explicit-formula inputs

The active theorem uses exactly the existing local hypothesis
`ChenEffective.dirichlet_seven_eighths`, plus Lean's standard axioms.
There are no BJS axioms, OpenAI imports, new external dependencies,
placeholders or native_decide proofs.

## Current result

`BJSStudyChen.lean` proves that every even N >= bjsStudyN0 is a prime plus
another prime or a product of two primes, with the exact cutoff

    bjsStudyN0 = 3^(3^171).

In natural double-exponential coordinates N0=exp(exp(H)), this is
H=171*log(3)+log(log(3)), approximately 187.956749.
`BJSStudyCompatibility.lean` recovers the exact original public Chen statement,
without using the original implicit Chen proof or the stronger counting theorem.
The verified positive end-to-end budget margin remains 0.050585.

## Why the cutoff decreased

`research/chen-dusart` proves the theta and signed reciprocal-prime prefix
bounds from 3^120 by an explicit formula and a numerical zero moment under
the permitted Dirichlet hypothesis. All analytic inputs are proved. No
finite-height RH hypothesis or numerical zero table is assumed.

`BJSStudyProducts.lean` uses that theorem to prove the relative Goldbach
sieve product bound with error 1/4000 at pre-sieve start U=3^120. It includes
the summable prime-square correction and the exact closed-left endpoint.
The geometry pays log(N)>=10^20*(1+2U). The existing finite analytic and
square/triple caps all fit below the common cutoff 3^(3^171).

`BJSProvedProductProfile.lean` retains the independent coarse power-saving
profile at 3^2652, under names beginning `bjsPower`. It no longer supplies
the active smaller-cutoff proof. The previous active cutoff was 3^(3^2700).

The older qualitative production theorem and the stronger 0.67 counting
cutoff are unchanged. No claim is made here of H=120, H=36, or H=29.

## Checking

Run `research/chen-bjs-study/check.ps1` after the established production
prerequisites are built. Its order first prepares the reciprocal-prime
foundations, then checks the local Dusart package, then the product,
counting, triple and Chen proofs. Existing artifacts can be audited with
`check.ps1 -FromModule AuditBJSStudy`.

`AuditBJSStudy.lean` checks the numerical cutoff, the exact old Chen statement,
axiom ledgers, absence of OpenAI imports, and the complete final proof closure
for unsafe declarations or unlisted axioms. `source-audit.ps1` independently
scans the local Lean sources. `research/chen-dusart/AuditDusart.lean` audits
the analytic replacement separately.

See `DUSART_STATUS.md` for the exact analytic result and source provenance.
The historical conditional low-cutoff snapshot remains documented in
`LOW_CUTOFF_STUDY.md`; the current proof no longer uses its interval axiom.