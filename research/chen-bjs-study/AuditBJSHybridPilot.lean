import BJSHybridMomentResidual
import BJSHybridProductBridge
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean Meta
set_option maxHeartbeats 0

run_elab do
  let standard := #[``propext,``Classical.choice,``Quot.sound]
  let allowed := standard
  for n in #[``ChenEffective.HybridProduct.improved_zero_kernel_norm,
      ``ChenEffective.HybridProduct.prime_power_gap_seventeen,
      ``ChenEffective.HybridProduct.hybrid_product_payment,
      ``ChenEffective.HybridProduct.smoothing_scalar] do
    let axs ← Lean.collectAxioms n
    unless axs.all standard.contains do throwError "Unexpected scalar axiom in {n}: {axs}"
  for n in #[``ChenEffective.HybridProduct.finite_head_moment_residual,
      ``ChenEffective.HybridProduct.proposed_head_pays_residual,
      ``ChenEffective.HybridProduct.hybrid_interval_product] do
    let axs ← Lean.collectAxioms n
    unless axs.size == allowed.size && axs.all allowed.contains do
      throwError "Unexpected analytic axiom in {n}: {axs}"
  let env ← getEnv
  let mut todo := #[``ChenEffective.HybridProduct.finite_head_moment_residual]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "Missing dependency: {n}"
    if ci.isUnsafe then throwError "Unsafe dependency: {n}"
    if ci matches .axiomInfo _ then
      unless allowed.contains n do throwError "Unlisted axiom: {n}"
    todo := todo ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque:=true) then todo := todo ++ v.getUsedConstants
  for n in #[``ChenEffective.dusart_xi_zero_moment_identity,
      ``ChenEffective.HybridProduct.improved_zero_kernel_norm] do
    unless seen.contains n do throwError "Actual improved moment producer absent: {n}"
  logInfo m!"Hybrid residual proof audit passed: {seen.size} constants; standard axioms only; Dirichlet is proved."
  logInfo "The finite head need not be complete. No finite RH or zero-count axiom was added."
  logInfo "Pilot data, zero boxes, numerical moment cap, analytic bridges and HybridPrefixWindow remain unverified inputs; no small-endpoint product theorem is claimed without its hypothesis."
