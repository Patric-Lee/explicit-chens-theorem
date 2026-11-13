import OAI.ChenDirichlet
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean Meta
set_option maxHeartbeats 0

run_elab do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  let root := ``ChenEffective.dirichlet_seven_eighths
  let axs ← Lean.collectAxioms root
  unless axs.all allowed.contains do throwError "Unapproved Dirichlet proof axioms: {axs}"
  let env ← getEnv
  let some rootInfo := env.find? root | throwError "Missing Dirichlet adapter"
  if rootInfo matches .axiomInfo _ then throwError "Dirichlet adapter is still an axiom"
  let mut todo := #[root]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if #["sorryAx","Lean.ofReduceBool","Lean.trustCompiler"].contains n.toString then
      throwError "Forbidden proof dependency: {n}"
    let some ci := env.find? n | throwError "Missing dependency: {n}"
    if ci.isUnsafe then throwError "Unsafe proof dependency: {n}"
    if ci matches .axiomInfo _ then
      unless allowed.contains n do throwError "Unapproved proof axiom: {n}"
    todo := todo ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque:=true) then todo := todo ++ v.getUsedConstants
  unless seen.contains ``OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re do
    throwError "Actual upstream Dirichlet theorem absent"
  logInfo m!"OpenAI Dirichlet proof audit passed: {seen.size} constants; standard Lean axioms only."

#print axioms ChenEffective.dirichlet_seven_eighths
