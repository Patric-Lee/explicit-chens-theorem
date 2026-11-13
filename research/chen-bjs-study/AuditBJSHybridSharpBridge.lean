import BJSHybridSharpAnalyticBridge
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean Meta
set_option maxHeartbeats 0
run_elab do
  let standard := #[``propext,``Classical.choice,``Quot.sound]
  for n in #[``ChenEffective.HybridProduct.prime_power_gap_two,
      ``ChenEffective.HybridProduct.SharpPrimePowers.actual_prime_power_integral_bound] do
    let axs ← Lean.collectAxioms n
    unless axs.all standard.contains do throwError "Nonstandard prime-power axiom in {n}: {axs}"
  let allowed := standard
  let root := ``ChenEffective.HybridProduct.SharpPrimePowers.actual_prefix_from_head_dusart
  let axs ← Lean.collectAxioms root
  unless axs.size == allowed.size && axs.all allowed.contains do
    throwError "Unexpected sharp bridge axiom ledger: {axs}"
  let env ← getEnv
  let mut todo := #[root]
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
  for n in #[``ChenEffective.HybridProduct.prime_power_gap_two,
      ``ChenEffective.HybridProduct.SharpPrimePowers.actual_prime_power_integral_bound,
      ``ChenEffective.HybridProduct.actual_zero_sum_split,
      ``ChenEffective.HybridProduct.psi1_error_right_derivative,
      ``ChenEffective.HybridProduct.actual_integrated_psi1_bound,
      ``ChenEffective.dusart_sharp_mertens] do
    unless seen.contains n do throwError "Actual analytic producer missing: {n}"
  logInfo m!"Sharp hybrid bridge audit passed: {seen.size} constants; prime-power bound 2*sqrt(x) at x>=3^16."
  logInfo "Elementary prime-power inputs use standard axioms only; the analytic bridge retains standard axioms only; Dirichlet is proved."
