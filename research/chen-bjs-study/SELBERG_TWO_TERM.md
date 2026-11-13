# Selberg two-term expansion

The kernel-checked theorem `ChenEffective.selberg_uniform_two_term_expansion`
in `BJSSelbergSquareRemainder.lean` proves, for every positive even integer
N and every integer R >= 1,

\[
\left|G_N(R)-\frac{\log R+c_N}{2\mathfrak S(N)}\right|
\le \frac{20\exp(1096+(\log N)/16)}{\sqrt R},
\qquad
c_N=\gamma+\sum_{p\mid N}\frac{\log p}{p-1}>0.
\]

Here the finite prime sum includes 2, and

\[
G_N(R)=\sum_{1\le d\le R}\operatorname{liuSelbergArithmetic}(N,d)
=\sum_{\substack{d\le R\\d\text{ squarefree}\\(d,N)=1}}
\prod_{p\mid d}\frac1{p-2}.
\]

The constant is explicit and uniform in R, with displayed dependence on N:
exp(1096+(log N)/16) = exp(1096) N^(1/16). There is no log R loss. An
absolute constant independent of both N and R is not asserted. For the Chen
scale R >= N^(1/4), the displayed error is at most
20 exp(1096) N^(-1/16). This comparison is explanatory algebra, not an
additional Lean cutoff theorem.

The exponent 1096 is a deliberately coarse, proved cap. This is a direct
formal proof of the expansion shape, not a claim to match the sharp
numerical remainder constants in Zuniga Alterman's Theorem 4.6.

## Proof components

1. `BJSSelbergSignedMoment.lean` uses an Euler product in the dual numbers to
   prove the exact signed logarithmic moment of the original correction:

   \[
   \sum_d c_N^{\mathrm{corr}}(d)\log d
   =-\frac1{2\mathfrak S(N)}\sum_{p\mid N}\frac{\log p}{p-1}.
   \]

2. `BJSSelbergTwoTermIdentity.lean` substitutes this moment and the already
   proved correction mass into the exact harmonic convolution. This proves
   the two-term identity with its actual residual, before estimating it.

3. `BJSHarmonicKernel.lean`, `BJSPowerTails.lean`,
   `BJSSquareHarmonic.lean`, and `BJSSquareHarmonicMass.lean` prove the
   harmonic head and logarithmic tail estimates. The complete square-kernel
   residual has absolute mass at most 20/sqrt(x) for every real x > 0,
   including the empty-sum range x < 1.

4. `BJSSelbergCriticalKernel.lean`, `BJSSelbergSquareKernel.lean`, and
   `BJSSelbergSquareConvolution.lean` prove the exact factorization of the
   original correction into a square-supported kernel and a multiplicative
   critical correction a_N. `BJSSelbergCriticalMass.lean` proves

   \[
   \sum_d |a_N(d)|\sqrt d\le\exp(1096+(\log N)/16).
   \]

5. `BJSSelbergSquareRemainder.lean` sums the absolute convolution residual
   through the divisor-antidiagonal equivalence. Absolute summability is
   proved before exchanging sums. The finite range is never substituted for
   an infinite sum without accounting for its tail.

`BJSConvolutionRemainder.lean` also records a reusable square-root transfer
lemma for other base kernels.

## Trust and integration

`AuditBJSSelbergExpansion.lean` traverses all proof dependencies and permits
only `propext`, `Classical.choice`, and `Quot.sound`. The expansion requires
no Dirichlet hypothesis, local analytic axiom, OpenAI import, or new Lake
dependency. The usual source audit also rejects proof placeholders and
compiler-based decision shortcuts.

Run `check.ps1 -FromModule BJSHarmonicKernel` to rebuild the package and its
audit. The expansion is now propagated through the actual square/triple bounds and final Chen existence theorem in `BJSExpandedChen.lean`; see [EXPANDED_CHEN.md](EXPANDED_CHEN.md). The final cutoff is unchanged because the independent lower-count geometry dominates.
