import OAI.AuditChenDirichlet
import AuditBJSTightBudget
import AuditBJSH30Conditional
import AuditBJSH30Triple
import AuditBJSHybridSharpBridge
import AuditDusart
import audit.AuditChen
import AuditBJSStudy
import audit.AuditElementaryMertens
import Lean.Util.CollectAxioms

open Lean Meta
set_option maxHeartbeats 0

run_elab do
  if debug.skipKernelTC.get (← getOptions) then
    throwError "Kernel type checking must be enabled"
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let conditional := standard ++
    #[``ChenEffective.H30Conditional.temporary_reciprocal_prefix_window]
  for n in #[``ChenEffective.dirichlet_seven_eighths,
      ``ChenEffective.TightBudget.chen,
      ``ChenEffective.TightBudget.original_chen,
      ``ChenEffective.bjsStudy_chen,
      ``ChenEffective.joint_chen_81,
      ``ChenEffective.expanded_chen] do
    let axs ← Lean.collectAxioms n
    unless axs.size == standard.size && axs.all standard.contains do
      throwError "Wrong standard-only axiom ledger for {n}: {axs}"
    logInfo m!"Standard-only proof: {n}; axioms {axs}"
  for n in #[``ChenEffective.H30Conditional.chen,
      ``ChenEffective.H30Conditional.original_chen] do
    let axs ← Lean.collectAxioms n
    unless axs.size == conditional.size && axs.all conditional.contains do
      throwError "Wrong conditional axiom ledger for {n}: {axs}"
    logInfo m!"Conditional proof: {n}; axioms {axs}"
  for n in #[``ChenEffective.TightBudget.original_chen,
      ``ChenEffective.H30Conditional.original_chen] do
    unless ← isDefEq (← getConstInfo n).type (← getConstInfo ``Goldbach.chen_theorem).type do
      throwError "Literal old Chen statement mismatch: {n}"
  let pairs := #[( ``ChenEffective.TightBudget.original_chen,
      ``ChenEffective.TightBudget.chen),
    (``ChenEffective.H30Conditional.original_chen,
      ``ChenEffective.H30Conditional.chen)]
  let env ← getEnv
  for (bridge, producer) in pairs do
    let mut todo := #[bridge]
    let mut seen : NameSet := {}
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      if #["Goldbach.chen_theorem",
          "MathlibNt.ChensTheorem.chens_theorem_unconditional",
          "sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler"].contains n.toString then
        throwError "Forbidden recovery proof dependency: {n}"
      let some ci := env.find? n | throwError "Missing recovery dependency: {n}"
      if ci.isUnsafe then throwError "Unsafe recovery dependency: {n}"
      todo := todo ++ ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then
        todo := todo ++ v.getUsedConstants
    unless seen.contains producer do
      throwError "The recovery proof does not use its numerical Chen theorem: {bridge}"
    unless seen.contains ``OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re do
      throwError "The actual OpenAI Dirichlet theorem is absent from {bridge}"
    logInfo m!"Recovery dependency audit: {bridge}; {seen.size} constants; numerical producer and actual Dirichlet proof present."
  let some ci := (← getEnv).find? ``ChenEffective.dirichlet_seven_eighths |
    throwError "Missing proved Dirichlet theorem"
  if ci matches .axiomInfo _ then throwError "Dirichlet is still an axiom"
  logInfo "Chen integration audit passed: Dirichlet is proved; both literal old Chen statements recovered."

#print axioms ChenEffective.TightBudget.chen
#print axioms ChenEffective.TightBudget.original_chen
#print axioms ChenEffective.H30Conditional.chen
#print axioms ChenEffective.H30Conditional.original_chen
