import BJSHybridAnalyticBridge
import BJSHybridPrimeCertificate
import BJSHybridPrimeBlock
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean Meta
set_option maxHeartbeats 0
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let root := ``ChenEffective.HybridProduct.actual_prefix_from_head_dusart
  let axs ← Lean.collectAxioms root
  unless axs.size == allowed.size && axs.all allowed.contains do
    throwError "Unexpected analytic bridge axiom ledger: {axs}"
  let env ← getEnv
  let mut todo := #[root,``ChenEffective.HybridProduct.prime_prefix_of_certificate,
    ``ChenEffective.HybridProduct.prime_block_of_certificate,
    ``ChenEffective.HybridProduct.actual_prefix_without_zero_table]
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
  for n in #[``ChenEffective.HybridProduct.actual_zero_sum_split,
      ``ChenEffective.HybridProduct.psi1_error_right_derivative,
      ``ChenEffective.HybridProduct.actual_theta_weighted_parts,
      ``ChenEffective.HybridProduct.actual_integrated_psi1_bound,
      ``ChenEffective.HybridProduct.actual_prime_power_integral_bound,
      ``ChenEffective.HybridProduct.actual_psi_step_bound,
      ``AnalyticNumberTheory.Mertens.mertensSecond_error_decomposition,
      ``ChenEffective.dusart_sharp_mertens] do
    unless seen.contains n do throwError "Actual analytic producer absent: {n}"
  logInfo m!"Actual hybrid analytic bridge audit passed: {seen.size} constants; standard axioms only; Dirichlet is proved."
  logInfo "This theorem still requires certified finite-head bounds. It does not discharge HybridPrefixWindow or claim H below 30."
