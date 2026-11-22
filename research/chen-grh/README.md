# Full Dirichlet GRH route: completed H < 13.37 Chen theorem

The current complete theorem has exact cutoff **3^580000**, with
H approximately **13.36483121014** and a Lean proof that H < 13.37.
Its exact statement is ChenEffective.GRH1337.chen_explicit; original_chen
has literally the original Goldbach.ChenTheorem type.

The actual weighted lower coefficient is 2.02575, the complete corrected
triple coefficient is 4.0002, and the representation margin is 0.02565.
The sole added axiom is full Dirichlet GRH. No additional analytic or numerical
input is assumed. The old H<14 result below remains available.

See [the numerical proof and reproduction commands](NUMERICAL_CHEN_H1337.md),
[the exact theorem and native audit](AuditGRH1337Chen.lean), and
[the source/object report](FINAL_GRH1337_CHEN_AUDIT.json).
The new analytic components are grouped in GRH1337Analytic.lean to avoid
repeated environment loading. Existing finite certificates are reused.

## Earlier H < 14 development

The sole external axiom is now
`ChenEffective.GRH.alpoge_dirichlet_grh` in
[GRHAssumption.lean](GRHAssumption.lean). It is exactly the critical-strip
`DirichletLZerosOnLine` statement in the
[Alpöge/Claude release](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/main/src/Statements.lean):

$$
  L(s,\chi)=0,\quad 0<\Re s<1
  \quad\Longrightarrow\quad \Re s=\tfrac12
$$

for every Dirichlet character of every nonzero modulus, at every height.
We assume this statement rather than import the large proof. No numerical,
distribution, sieve or Chen estimate has been added as an axiom. Package and
toolchain pins are unchanged, and there is no `native_decide` in this route.

The old `PlattWindow.platt_modulus_one_finite_RH` declaration is a **theorem**
derived from this axiom. Its API is retained so the existing finite
certificates and analytic tail continue to apply. Platt is not a second
axiom. The prior Platt-only audit reports describe historical snapshots.

## Checked analytic and numerical progress

[GRHAbsoluteZeroSum.lean](GRHAbsoluteZeroSum.lean) exposes the sum of absolute
values already bounded inside the calr3 zero-sum argument. Its finite-RH
premise is explicit and it uses only standard Lean axioms.

[GRHSmoothedCharacters.lean](GRHSmoothedCharacters.lean) uses full GRH to put
**all** nontrivial zeros, including the high-zero tail, on the square-root
scale. For the existing Gaussian character sum `Ssum χ 0 x`,
[GRHCharacterConstants.lean](GRHCharacterConstants.lean) proves

$$
 \lVert S_\chi(0,x)\rVert
 \le 10^7(1+\log q)\sqrt x\qquad(x\ge1)
$$

for primitive nonprincipal characters modulo q. This is a smoothed estimate;
it is not yet a sharp interval or arithmetic-progression prime-count bound.

[GRH14ScalarBudget.lean](GRH14ScalarBudget.lean) fixes the proposed cutoff

$$
 N_*=3^{1{,}000{,}000}<\exp(\exp(14)),
 \qquad H_*\approx13.90955839.
$$

It proves that if L >= 1,000,000, C <= 10^7, k <= 12 and alpha >= 1/5000,

$$
 C L^k e^{-\alpha L}\le10^{-6}.
$$

The strengthened `distribution_error_payment` permits C <= 10^30 when
alpha >= 1/1000, at the same cutoff and with the same error allowance.

[GRHLogDerivative.lean](GRHLogDerivative.lean) proves the quantitative
full-GRH logarithmic-derivative estimate

$$
 \left|\frac{L'}L(s,\chi)\right|
 \le\frac{64}{a^2}\log\bigl(16q(|\Im s|+4)\bigr),
 \qquad \tfrac12+a\le\Re s\le2,
$$

for every nonprincipal character and 0 < a <= 1. The regularized principal
analogue is in [GRHZetaStrip.lean](GRHZetaStrip.lean).
[GRHMellin.lean](GRHMellin.lean) proves the complementary bounds for the
actual smoothing kernel:

$$
 |\mathcal M\phi_\varepsilon(s)|
 \le\min\left\{\frac{768}{|s|},
                  \frac{768}{\varepsilon|s|^2}\right\}.
$$

[GRHContourBound.lean](GRHContourBound.lean) uses the first bound on the
left edge and gives `4608 J x^sigma log(1+T)`, rather than a bound
proportional to T/epsilon. The actual contour identities, principal residue,
horizontal and right tails, and smoothing removal are proved in
[GRHSharpPerron.lean](GRHSharpPerron.lean),
[GRHPrefix.lean](GRHPrefix.lean),
[GRHPrincipal.lean](GRHPrincipal.lean), and
[GRHPrincipalPrefix.lean](GRHPrincipalPrefix.lean). Their numerical results,
for x >= 1 and log x >= 10, are

$$
 \left|\sum_{n\le x}\Lambda(n)\chi(n)\right|
 \le10^{13}(\log q+\log x)^2x^{0.501},\quad\chi\ne1,
 \qquad
 |\psi(x)-x|\le10^{14}(\log x)^2x^{0.501}.
$$

The nonprincipal result includes imprimitive characters.
[GRHArithmeticProgressions.lean](GRHArithmeticProgressions.lean) uses actual
character orthogonality and the principal bad-prime-power correction to prove

$$
 \left|\psi(N;q,a)-\frac N{\varphi(q)}\right|
 \le10^{15}(\log q+\log N)^3N^{0.501}
 \qquad(N\ge2,\ \log N\ge10,\ q>0,\ (a,q)=1).
$$

This pointwise Chebyshev estimate is extended as follows.
[GRHAPMaxima.lean](GRHAPMaxima.lean) proves the same bound for all prefixes
through N, handling the small range by an unconditional elementary bound.
[GRHPrimeAPMaxima.lean](GRHPrimeAPMaxima.lean) then proves the actual
`standardPrimeAPPrefixMaxError` bound with coefficient 10^16, including
prime powers, Abel amplification and the true logarithmic integral.

[GRHWeightedDistribution.lean](GRHWeightedDistribution.lean) proves the
squarefree weighted estimate

$$
 \sum_{d\in S}3^{\omega(d)}E_\pi(N,d)
 \le10^{-12}\frac N{(\log N)^2},
 \quad S\subseteq[1,D],\quad D\le N^{0.498},\quad N\ge N_*.
$$

Here E_pi is the project's actual maximal prime-count AP error. The proof
uses the elementary mean of the ordered divisor function of order three,
not a Li--Liu analytic result. The exact truncated pre-sieve family connections are proved in
`GRH14BaseDistribution` and `GRH14MediumDistribution`. The complete
triple estimate uses the separate weighted Pan assembly described below.

[GRH14SelbergBudget.lean](GRH14SelbergBudget.lean) proves, with only standard
Lean axioms, the actual Selberg denominator bound uniformly in the radius
parameter epsilon <= 1/1000, for positive even N >= N_*:

$$
 G_\varepsilon(N)\ge
 \frac{\log N}{8.1\,\mathfrak S(N)}.
$$

This permits joint optimization instead of retaining the old fixed
epsilon = 10^-10. It does not prove the complete triple remainder.

## Completed numerical lower count at H < 14

The released theorem `ChenEffective.GRH14.weighted_lower` proves

$$
 W(N)\ge2.02575\,\mathfrak S(N)\frac{N}{(\log N)^2}
 \quad(N\ge3^{1\,000\,000},\ N\text{ even}).
$$

It uses exactly full Dirichlet GRH and the standard Lean axioms. The
existing certified product window is proved, not an extra hypothesis in
the released theorem. See the [complete lower-count approach and statements](NUMERICAL_LOWER_H14.md)
and [final lower audit](FINAL_GRH14_LOWER_AUDIT.json).

The proof retains the product start 4,000,000 and truncates the pre-sieve
expansion at floor(N^(1/200)). The actual base and medium-prime truncated
remainders are each at most 3e-12 N/log(N)^2, including non-reduced primes
q dividing N. The source mass uses a square-root Mertens tolerance threshold.
Sharper sieve-factor comparisons retain the cancellation of exp(gamma)
with exp(-gamma). Both 64-cell rational kernel/hat certificates are checked
by Lean without native compiler trust.

**The complete H<14 Chen existence theorem is now proved and audited.**
`ChenEffective.GRH14.triple_upper` bounds the actual corrected triple
penalty by 3.993 M(N) at the same cutoff. Together with the checked lower
count, this gives the positive representation margin 0.02925 M(N).
`ChenEffective.GRH14.original_chen` recovers exactly
`Goldbach.ChenTheorem` from the new explicit theorem. Full Dirichlet GRH
remains the sole added axiom. See the [complete proof and budget](NUMERICAL_CHEN_H14.md)
and [final source/object and semantic audit](FINAL_GRH14_CHEN_AUDIT.json).

The older small-start product study remains a research record. Its
counterexample at prime 1543 is proved, but reducing the product start is
not needed by the completed truncated lower-count route.

## Reproduction

The serial full H<29 recheck under the sole full Dirichlet-GRH axiom
completed successfully on November 20, 2026, including the original-Chen
recoveries and integration audit. Its source/object provenance is recorded
in [FINAL_CHEN_GRH_AUDIT.json](FINAL_CHEN_GRH_AUDIT.json).

The numerical H<14 lower count and its complete transitive dependency audit
are checked in `AuditGRH14NumericalLower`. Its source/object provenance
is recorded in `FINAL_GRH14_LOWER_AUDIT.json`. The completed existence
theorem and its original-statement recovery are checked in `AuditGRH14Chen`;
see `FINAL_GRH14_CHEN_AUDIT.json` and the reproduction commands in the
[complete proof notes](NUMERICAL_CHEN_H14.md).

The smaller analytic check uses the `grhstrip` build tag and
`research/chen-grh/tools/AuditCompletedGRHAnalytic.mjs`; after it completes,
the report is `FINAL_GRH_ANALYTIC_AUDIT.json`. That historical report predates the completed H<14 counting assembly.
The complete older Chen recheck uses `fullgrh`
and the commands below.

Use the existing pinned Lean environment and source builder:

```powershell
$env:CHEN_BUILD_TAG = 'fullgrh'
$env:CHEN_BUILD_JOBS = '1'
node --expose-gc OpenAI/tools/build-source.mjs AuditGRHAnalytic AuditBJSH29Conditional AuditBJSTightBudget OAI.AuditChenIntegration
node research/chen-grh/tools/AuditCompletedGRHChen.mjs $PWD
```

`AuditGRHAnalytic` traverses the proof dependencies, rejects placeholders,
unsafe proofs and native compiler trust, and checks which results are
standard-only versus full-GRH-dependent. The final source/object report is
`FINAL_CHEN_GRH_AUDIT.json` after the full build and audit finish. It certifies
the existing H<29 Chen theorem and the new analytic progress, **not H<14**.
The existing 15+ hour finite-certificate build and its documented memory
requirements remain relevant to fresh builds of that certificate route;
the large Alpöge proof is not imported or rebuilt.
