import BJSHybridSievePacked
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean Meta
set_option maxHeartbeats 0
run_elab do
  let standard := #[``propext,``Classical.choice,``Quot.sound]
  let roots := #[``ChenEffective.HybridProduct.BitSieve.reciprocal_prefix_of_sieve_certificate,
    ``ChenEffective.HybridProduct.BitSieve.reciprocal_block_of_sieve_certificate,
    ``ChenEffective.HybridProduct.BitSieve.isSieve_of_sieveK_eq,
    ``ChenEffective.HybridProduct.BitSieve.fixedSieveRange_add,
    ``ChenEffective.HybridProduct.BitSieve.reciprocal_prefix_of_packed_certificate,
    ``ChenEffective.HybridProduct.BitSieve.reciprocal_block_of_packed_certificate,
    ``ChenEffective.HybridProduct.BitSieve.packedRange_add]
  for n in roots do
    let axs ← Lean.collectAxioms n
    unless axs.all standard.contains do throwError "Unexpected sieve axiom in {n}: {axs}"
  let env ← getEnv
  let mut todo := roots
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "Missing dependency: {n}"
    if ci.isUnsafe then throwError "Unsafe sieve dependency: {n}"
    if ci matches .axiomInfo _ then
      unless standard.contains n do throwError "Unlisted sieve axiom: {n}"
    todo := todo ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque:=true) then todo := todo ++ v.getUsedConstants
  for n in #[``ChenEffective.HybridProduct.BitSieve.sieveK_testBit_iff,
      ``ChenEffective.HybridProduct.BitSieve.fixedSievePrefix_eq,
      ``ChenEffective.HybridProduct.BitSieve.fixedSieveBlock_eq,
      ``ChenEffective.HybridProduct.BitSieve.fixedSieveRange_of_packed,
      ``ChenEffective.HybridProduct.reciprocal_floor_bounds,
      ``AnalyticNumberTheory.Mertens.primeReciprocalSum] do
    unless seen.contains n do throwError "Actual sieve/sum producer absent: {n}"
  logInfo m!"Bitset sieve and actual reciprocal-prefix/block adapters audited: {seen.size} constants; standard axioms only."
