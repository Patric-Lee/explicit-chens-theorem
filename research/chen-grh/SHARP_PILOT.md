# Smaller-cutoff budget pilot

This file records the earlier budget pilot. Its propagation is now complete:
the [new Chen theorem](NUMERICAL_CHEN_H1337.md) has exact cutoff **3^580000**,
H approximately 13.364831, with GRH as the sole added axiom.

Five new modules have passed Lean checking, with only standard Lean axioms:

- GRHSharpRootMoment: the reciprocal-square-root prime moment through
  4,000,000 is at most 1173, replacing 1700. Each interval uses its own
  logarithm lower bound; no prime enumeration is needed.
- GRHSharpDivisorMoments: corresponding squarefree divisor moments are
  at most exp(1173) and exp(1468), replacing exp(1700) and exp(2126).
- GRHSharpTruncationPayment: the complete medium-tail envelope
  336 L^6 exp(1468 + log(2)/2 - L/400) is at most 10^-12 for L >= 637000.
- GRHSharpCutoffBudget: N >= 3^580000 implies log(N) >= 637000;
  this candidate cutoff is strictly below exp(exp(13.37)). Its actual
  double-log coordinate is approximately 13.364831.
- GRHSharpPanPayment: for L >= 637000, A <= 10^17, k <= 73 and
  alpha >= 1/512, A L^k exp(-alpha L) <= 1. This specializes the old
  unused degree-100 budget to a smaller useful range.

The machine-readable source/object receipts are in SHARP_PILOT_AUDIT.json.
There are no new axioms, native_decide uses, or package dependencies.

At the time of the pilot, remaining propagation was: connect the sharper moments to the actual base and
medium-prime aggregate tails; specialize the high-conductor and principal
Pan thresholds to the new target; retune both numerical integration grids;
recheck lower and complete triple coefficients jointly; assemble and audit
the smaller-cutoff Chen theorem and its original implicit corollary.
The stronger already-proved GRH character prefix estimate can replace the
old seven-eighths-based moving estimate if a subsequent lower target needs it.
