import NumericalElementaryMertens
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean Meta
set_option maxHeartbeats 0

run_elab do
  if debug.skipKernelTC.get (← getOptions) then
    throwError "Kernel type checking must be enabled"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let roots := #[``ChenEffective.ElementaryMertens.sum_log_prime_div_eq_log,
    ``ChenEffective.ElementaryMertens.prime_reciprocal_error_ten]
  for n in roots do
    let axs ← Lean.collectAxioms n
    unless axs.size == allowed.size && axs.all allowed.contains do
      throwError "Unexpected elementary Mertens axioms: {n}: {axs}"
  let env := (← getEnv).setExporting false
  for n in env.header.moduleNames do
    let s := n.toString
    if #["PrimeNumberTheoremAnd", "IEANTN", "MathlibNt", "AnalyticNumberTheory",
        "OpenAI", "ComparatorChallenges", "OAI"].any (fun p => s == p || s.startsWith (p ++ ".")) then
      throwError "Unexpected imported project module: {n}"
  let mut todo := roots
  let mut seen : NameSet := {}
  let mut axioms : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "Missing dependency: {n}"
    if ci.isUnsafe then throwError "Unsafe dependency: {n}"
    match ci with
    | .axiomInfo _ =>
      unless allowed.contains n do throwError "Unexpected traversed axiom: {n}"
      axioms := axioms.insert n
    | _ => pure ()
    todo := todo ++ ci.type.getUsedConstants
    if let some value := ci.value? (allowOpaque := true) then
      todo := todo ++ value.getUsedConstants
  unless axioms.size == 3 do throwError "Wrong axiom count"
  logInfo m!"Elementary Mertens audit passed: {seen.size} proof dependencies, exactly standard axioms, no unsafe dependencies or project inputs."

#check ChenEffective.ElementaryMertens.prime_reciprocal_error_ten
