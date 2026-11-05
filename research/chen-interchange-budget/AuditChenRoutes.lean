import ChenRouteMixing
import Goldbach.Theorem
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean Meta
set_option maxHeartbeats 0

example : ChenEffective.productionRouteCertificate.cutoff=3^(3^2900) :=
  ChenEffective.qualitativeGeometryThreshold_eq
example : ChenEffective.bjsRouteCertificate.cutoff=3^(3^171) :=
  ChenEffective.bjsStudyGeometryThreshold_eq

run_elab do
  if debug.skipKernelTC.get (← getOptions) then throwError "Kernel checking is disabled"
  let standard := #[``propext,``Classical.choice,``Quot.sound]
  let dirichlet := standard ++ #[``ChenEffective.dirichlet_seven_eighths]
  let provisional := dirichlet ++ #[``ChenEffective.bjsStudy_interval]
  for n in #[``ChenEffective.chen_route_count,``ChenEffective.chen_route_original,
      ``ChenEffective.chen_route_margin_decomposition,``ChenEffective.chen_route_thresholds_iff,
      ``ChenEffective.chen_route_triple_improvement,``ChenEffective.route_source_triple_error] do
    let axs ← Lean.collectAxioms n
    unless axs.all standard.contains do throwError "Unexpected generic-budget axiom: {n}: {axs}"
  for (n,allowed) in #[( ``ChenEffective.production_route_original,dirichlet),
      (``ChenEffective.bjs_route_original,provisional),(``ChenEffective.mixed_route_original,provisional)] do
    unless ← isDefEq (← getConstInfo n).type (← getConstInfo ``Goldbach.chen_theorem).type do
      throwError "Original statement mismatch: {n}"
    let axs ← Lean.collectAxioms n
    unless axs.size==allowed.size && axs.all allowed.contains do
      throwError "Wrong adapter axiom ledger: {n}: {axs}"
    logInfo m!"Exact original Chen statement and axiom ledger passed: {n}"
  let env := (← getEnv).setExporting false
  for m in env.header.moduleNames do
    if #["OAI","OpenAI","ComparatorChallenges"].any
        (fun s => m.toString==s || m.toString.startsWith (s++".")) then
      throwError "Forbidden OpenAI import: {m}"
  let forbidden := #[``Goldbach.chen_theorem,
    ``MathlibNt.ChensTheorem.chens_theorem_unconditional,
    `ChenEffective.qualitative_chen,`ChenEffective.bjsStudy_chen,
    `ChenEffective.numerical_chen,`ChenEffective.numerical_chen_representation_count]
  let mut todo := #[``ChenEffective.production_route_original,
    ``ChenEffective.bjs_route_original,``ChenEffective.mixed_route_original]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if forbidden.contains n then throwError "Budget wraps an old final Chen proof: {n}"
    let some ci := env.find? n | throwError "Missing dependency: {n}"
    if ci.isUnsafe then throwError "Unsafe dependency: {n}"
    if ci matches .axiomInfo _ then
      unless provisional.contains n do throwError "Unlisted axiom: {n}"
    todo := todo ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque:=true) then todo := todo ++ v.getUsedConstants
  logInfo m!"Interchangeable budget audit passed ({seen.size} proof/type dependencies); no old final theorem used."
  logInfo "Generic budget has no new axioms. Production uses Dirichlet only; BJS/mixed routes retain only the temporary ordered interval assumption; both density adapters are proved."
