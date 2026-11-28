# H = 10: finite quarter-moment and actual tail assembly

This is a component of the H = 10 research route. It does not prove Chen's
theorem at that cutoff. The completed Chen cutoff remains `3^145000`,
corresponding to H approximately 11.97854. The component verification record
is `QUARTER_TAIL_COMPONENT_CHECK.json`; its checks must pass before these
components are described as verified.

For square-free Q whose prime divisors satisfy 2 < p <= 4,000,000, the new
finite certificate proves the two bounds

$$
\sum_{d\mid Q}d^{-3/4}\le e^{17.99},\qquad
\sum_{d\mid Q}d^{1/4}\nu(d)\le e^{17.99},
\quad \nu(d)=\prod_{p\mid d}\frac1{p-1}.
$$

The shared logarithmic envelope is

$$
\sum_{2<p\le4\cdot10^6}
\log\left(1+c(p)p^{-3/4}+\mathbf1_{p=3}p^{-1/4}\right)<17.99,
\qquad
c(p)=\begin{cases}1.26&p\le100,\\1.01&p>100.\end{cases}
$$

There are 508 disjoint, kernel-checked sieve shards. Their integer upper
enclosures total exactly 17.982053214203. Integer fourth-root bounds and
degree-three or degree-seven Taylor inequalities connect those enclosures
to the real logarithms. Sixteen aggregation modules combine the shards;
the square-free Euler identity then gives the two divisor moments.
All finite checks use `decide +kernel`.

Let S be the actual source bounding sieve, Q its prime product below four
million, and R its remaining prime product. For N > 2 even, log N >= 1,
D >= 1 and C >= 1, the resulting absolute tail estimate is

$$
\frac1{C^{1/4}}
\sum_{\substack{d\mid R\\d<D}}\sum_{a\mid Q}
a^{1/4}|S.\mathrm{rem}(ad)|
\le
\frac{11N e^{17.99}(1+\log D)^2}{C^{1/4}}.
$$

For weights supported below D with absolute value at most one, the actual
pre-sieved error is bounded by the original distribution sum at range CD
plus this tail. The distribution sum is retained explicitly; no sharper
distribution estimate is asserted by this component.

The analogous conditioned tails, summed over the actual medium primes and
allowing individual levels 1 <= D(q) <= N, satisfy, with L = log N >= 2400,

$$
\sum_q\mathrm{Tail}_q
\le\frac{25.41N e^{17.99}(1+L)^2}{C^{1/4}}
\le\frac{N}{L^2}\frac{26L^4 e^{17.99}}{C^{1/4}}.
$$

The proposed H = 10 budget uses 16L in place of 26L^4. That improvement
is **not proved** by the finite moment certificate. A diagnostic at
L = 22026 changes the geometry loss from about 0.09661 to 0.15197 when
16L is replaced by 26L^4, with other modeled inputs held fixed. The latter
does not leave a positive margin in the current model. These are numerical
diagnostics, not impossibility results for other parameter choices.

A follow-up [quadratic-tail study](H10_QUADRATIC_TAIL_TARGETS.json) shows
that 16L is not the only sufficient target. With the existing 64-cell
kernel profile, tail prefactor 0.05 L^2, error allowance tau = 0.001,
theta = 0.00765, delta = 0.00224 and geometry loss g = 0.1, the model gives
lower coefficient 1.9949355, triple coefficient approximately 3.97903654
and positive margin approximately 0.00541723. This retains the unproved
weighted distribution target 10 L^4 exp(-delta L). The quadratic tail
prefactor itself is also unproved. It is a less demanding alternative to
16L, not a newly established Chen estimate.

### Candidate interpolation bridge (not yet formalized)

For nonnegative x_a, B and Gamma, suppose
x_a <= B nu(a), x_a <= Gamma, and a nu(a) >= 1. Then

$$
x_a^4\le\Gamma B^3\nu(a)^3
\le\Gamma B^3a\nu(a)^4,
\qquad
\sum_{a\mid Q}x_a\le
\Gamma^{1/4}B^{3/4}e^{17.99}.
$$

This is why the quarter-moment certificate can support a sharper route
than the currently assembled absolute tail. Applying the interpolation
to a uniform GRH AP remainder bound, retaining the inverse-log source
mass estimate, and replacing the generic divisor mass by a relative
Euler-product bound could recover the needed factors.

As a diagnostic only, take the remaining-divisor mass <= 0.0066 L,
the trivial majorant coefficient b = 1.001, a uniform remainder bound
Gamma <= G sqrt(N) A with A <= 10,880,000 + 2L, and
qD <= sqrt(N)/(C N^delta). After the medium-prime sum, the normalized
prefactor would be bounded by

$$
1.21\cdot0.0066\,b^{3/4}L^3(GA)^{1/4}e^{-\delta L/4}.
$$

At L = 22026 and delta = 0.00224, this is approximately 0.04450 L^2
when G = 1, below the sufficient 0.05 L^2 target. These hypotheses are
**proof obligations**, not added axioms or established components of the
current Chen proof. In particular, the currently available coarse AP
bound, with constant 10^16, three logarithmic powers and N^0.501, does
not supply the required sharp uniform Gamma bound.

What remains for H = 10:

1. Recover the missing logarithmic factors in the aggregate tail, aiming
   first at the sufficient 0.05 L^2 target. A
   relative Euler-product bound can improve the generic divisor mass;
   sharper counting or a tail estimate using the sieve-weight structure
   is then needed for further savings.
2. Prove the specialized weighted distribution bound, including the
   convolution/QD remainder. A pointwise GRH estimate for primes in
   progressions does not discharge that obligation.
3. Replace the old source and Selberg-denominator interface thresholds
   with estimates valid at this scale.
4. Prove the actual lower and triple count inequalities on the finite
   bands, paste them to the existing large-N theorem, recover the original
   implicit statement, and audit the final Chen theorem.

The component audit permits only Lean's standard axioms. The full Chen
route continues to permit full Dirichlet GRH as its sole additional axiom.
No dependency or numerical assumption is added here.

## External comparison checked November 27, 2026

The current sthubbar Chen entry still states H = 13.375, with Theorems 5,
6, 7 and the explicit linear sieve as hypotheses in addition to GRH.
The latest Chen-specific change found, November 5, adds a note about the
fixed-level versus all-level sieve condition; it does not improve H.

- [Current theorem and scope](https://github.com/sthubbar/goldbach-lean/blob/main/entries/bordignonstarichkova2024grh/formalization.yaml)
- [Sieve-input note](https://github.com/sthubbar/goldbach-lean/blob/main/entries/bordignonstarichkova2024grh/NOTE-sieve-input.md)
- [Preprint repository](https://github.com/sthubbar/lean-lab-preprints)

## Reproduction

Use the repository's existing pinned Lean environment. This campaign reuses
the checked finite shards when their source and object hashes match.

```powershell
$env:CHEN_BUILD_TAG = 'quarterassembly'
$env:CHEN_BUILD_JOBS = '2'
$env:CHEN_BUILD_COMPACT_LEDGER = '1'
node --expose-gc OpenAI/tools/build-source.mjs AuditGRHQuarterTail
node research/chen-grh/tools/CheckQuarterTail.mjs $PWD
```

The transitive audit checks for unexpected axioms, placeholders, unsafe
proof dependencies, native compiler trust, and disabled kernel checking.
The accompanying checker verifies interval coverage, the exact integer
total, source/object provenance, pinned dependencies, and successful audit
output. This is a component audit, not a rerun of the complete Chen audit.
