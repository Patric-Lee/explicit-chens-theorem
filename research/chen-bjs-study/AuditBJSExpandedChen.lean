import BJSExpandedChen
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean Meta
set_option maxHeartbeats 0

example : ChenEffective.expandedSelbergThreshold=3^1000000 :=
  ChenEffective.expandedSelbergThreshold_eq
example : ChenEffective.expandedChenN0=3^(3^171) := ChenEffective.expandedChenN0_eq

run_elab do
  let standard := #[``propext,``Classical.choice,``Quot.sound]
  let allowed := standard
  for n in #[``ChenEffective.expanded_singular_series_cap,
      ``ChenEffective.expanded_selberg_normalized_error,
      ``ChenEffective.expanded_selberg_denominator,
      ``ChenEffective.expanded_inverse_log_payment,
      ``ChenEffective.expanded_chen_margin,
      ``ChenEffective.expanded_chen_budget_iff,
      ``ChenEffective.expanded_chen_K_near_boundary] do
    let axs ← Lean.collectAxioms n
    unless axs.all standard.contains do throwError "Nonstandard component axiom in {n}: {axs}"
  let axs ← Lean.collectAxioms ``ChenEffective.expanded_chen
  unless axs.size == allowed.size && axs.all allowed.contains do
    throwError "Wrong expanded Chen axiom ledger: {axs}"
  let env ← getEnv
  let forbidden := #[``ChenEffective.bjsStudy_chen,``ChenEffective.joint_chen_81]
  let mut todo := #[``ChenEffective.expanded_original_chen]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if forbidden.contains n then throwError "Old final Chen proof used: {n}"
    let some ci := env.find? n | throwError "Missing dependency: {n}"
    if ci.isUnsafe then throwError "Unsafe dependency: {n}"
    if ci matches .axiomInfo _ then
      unless allowed.contains n do throwError "Unlisted axiom: {n}"
    todo := todo ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque:=true) then todo := todo ++ v.getUsedConstants
  unless seen.contains ``ChenEffective.selberg_uniform_two_term_expansion do
    throwError "The new expansion is not in the final proof closure"
  logInfo m!"Expanded Chen proof traversal passed: {seen.size} constants; standard axioms only; Dirichlet is proved."
  logInfo "The new two-term expansion supplies the denominator; old final Chen proofs are excluded."
  logInfo "Denominator cutoff 3^1000000; final cutoff 3^(3^171); optimized K=8.2257261896036; remainder allocation 10^-40."
