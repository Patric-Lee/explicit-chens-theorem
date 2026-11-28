import Lean.Util.CollectAxioms
import GRHConditionedQuarterTail

open Lean Meta
set_option maxHeartbeats 0
run_elab do
  if debug.skipKernelTC.get (← getOptions) then
    throwError "Kernel checking must be enabled"
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  let roots := #[``ChenEffective.H10Band.quarter_prime_envelope_cap,
    ``ChenEffective.H10Band.reciprocal_quarter_divisor_moment,
    ``ChenEffective.H10Band.density_quarter_divisor_moment,
    ``ChenEffective.H10Band.source_quarter_divisor_moments,
    ``ChenEffective.H10Band.source_quarter_tail_absolute,
    ``ChenEffective.H10Band.source_errSum_quarter,
    ``ChenEffective.H10Band.medium_quarter_tail_normalized]
  for root in roots do
    let axs ← Lean.collectAxioms root
    unless axs.all allowed.contains do
      throwError "Unexpected axioms for {root}: {axs}"
    logInfo m!"Quarter-moment axiom closure {root}: {axs}"
  let mut todo := roots
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if #["sorryAx","Lean.ofReduceBool","Lean.trustCompiler"].contains n.toString then
      throwError "Forbidden proof dependency {n}"
    let some ci := (←getEnv).find? n | throwError "Missing dependency {n}"
    if ci.isUnsafe then throwError "Unsafe proof dependency {n}"
    if ci matches .axiomInfo _ then
      unless allowed.contains n do throwError "Unlisted axiom {n}"
    todo := todo ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque:=true) then
      todo := todo ++ v.getUsedConstants
  logInfo m!"Quarter-moment and actual source-tail audit passed: {seen.size} transitive constants."
  logInfo "This is a component audit; no Chen theorem at H=10 or 16L prefactor is asserted."
