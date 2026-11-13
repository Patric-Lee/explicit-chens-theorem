# Minimal PrimeCert sieve port: provenance

Upstream: https://github.com/b-mehta/PrimeCert
Pinned commit: d84a15cacfdc45ae1e96e56dd58158f871787870

The original root MIT license is preserved in LICENSE.PrimeCert. The source
files also carry Apache-2.0 notices; these notices are retained, with the
repository's Apache-2.0 LICENSE. Relevant original notices:

- Sieve.lean and SieveCorrect.lean: Copyright (c) 2026 Bhavik Mehta.
  Authors: Bhavik Mehta.
- ForMathlib.lean: Copyright (c) 2025 Kenny Lau, Bhavik Mehta.
  Authors: Kenny Lau, Bhavik Mehta.
- ForLean.lean: Copyright (c) 2022 Bhavik Mehta.
  Authors: Bhavik Mehta.

Mapping:

| Local module | Upstream material |
| --- | --- |
| BJSHybridSieveCore | PrimeCert/Sieve.lean |
| BJSHybridSieveHelpers | bitwise subtraction and prime mod-6 helpers from ForMathlib.lean; the definitional div normalization from ForLean.lean |
| BJSHybridSieveCorrect | PrimeCert/SieveCorrect.lean |

The namespace is local: ChenEffective.HybridProduct.BitSieve. Module/export
syntax and a few newer lemma names were adapted for Lean 4.33.0-rc1. Imports
use the existing Mathlib only. No PrimeCert, Hex, OpenAI or new Lake package
is imported. The source version's 32-round mask and its endpoint bound are
preserved; this is not yet a segmented sieve through 2e10.

BJSHybridSieveSums, BJSHybridSieveBlocks, BJSHybridSievePacked, the generator,
benchmark driver and audits supply the local reciprocal-sum integration.
The generator is untrusted. Every emitted sieve transition and weighted sum
is checked by kernel reduction. The packed count/sum decoding is a theorem,
with explicit bounds preventing an aliased count.
