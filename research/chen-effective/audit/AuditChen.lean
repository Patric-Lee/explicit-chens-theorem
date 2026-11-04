import NumericalChenCompatibility
import NumericalC1SingleExponential
-- Only this audit fixture imports the old proofs, to compare declaration types.
import Goldbach.Theorem
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean Meta
set_option maxHeartbeats 0

run_elab do
  if debug.skipKernelTC.get (← getOptions) then
    throwError "Kernel type checking must be enabled"
  let pairs : Array (Name × Name) := #[
    (``ChenEffective.numerical_implies_original_chen, ``Goldbach.chen_theorem),
    (``ChenEffective.numerical_implies_original_internal_chen,
      ``MathlibNt.ChensTheorem.chens_theorem_unconditional),
    (``ChenEffective.numerical_implies_original_representation_bound,
      ``MathlibNt.ChensTheorem.chen_good_representations_lower_bound_unconditional),
    (``ChenEffective.numerical_implies_original_representation_bound,
      ``Goldbach.representation_lower_bound)]
  for (newName, oldName) in pairs do
    unless ← isDefEq (← getConstInfo newName).type (← getConstInfo oldName).type do
      throwError "Statement mismatch: {newName} versus {oldName}"
    logInfo m!"Exact original statement recovered: {oldName}"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound,
    ``ChenEffective.dirichlet_seven_eighths]
  let audited : Array Name := #[
    ``ChenEffective.numerical_chen,
    ``ChenEffective.numerical_chen_representation_count,
    ``ChenEffective.numerical_chen_above_tower,
    ``ChenEffective.numerical_count_above_tower,
    ``ChenEffective.numerical_implies_original_chen,
    ``ChenEffective.numerical_implies_original_internal_chen,
    ``ChenEffective.numerical_implies_original_representation_bound]
  for n in audited do
    let axs ← Lean.collectAxioms n
    unless axs.size == allowed.size && axs.all allowed.contains do
      throwError "Unexpected axioms for {n}: {axs}"
    logInfo m!"Exact four-axiom whitelist passed: {n}"
  for n in #[``ChenEffective.numerical_nLower_tower, ``ChenEffective.numerical_N0_tower] do
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a && a != ``ChenEffective.dirichlet_seven_eighths) do
      throwError "Unexpected threshold axioms for {n}: {axs}"
  for n in #[``ChenEffective.numerical_mertens_all,
      ``ChenEffective.numerical_source_local_product,
      ``ChenEffective.numericalLocalProductK_eq,
      ``ChenEffective.numericalLocalProductK_lt,
      ``ChenEffective.numerical_Qhat_le_hat,
      ``ChenEffective.numerical_sharp_hat_profile,
      ``ChenEffective.caseBSourceC1_eq,
      ``ChenEffective.numericalSuzukiC1_single_exp_cap] do
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a && a != ``ChenEffective.dirichlet_seven_eighths) do
      throwError "Unexpected elementary product axioms for {n}: {axs}"
  logInfo "Elementary Mertens, local-product, and improved C1 bounds use only standard axioms."
  -- Independently traverse proof/type references: none of the old implicit
  -- theorem proofs may supply the numerical theorem or its compatibility bridges.
  let forbidden := #[``Goldbach.chen_theorem, ``Goldbach.representation_lower_bound,
    ``MathlibNt.ChensTheorem.chens_theorem_unconditional,
    ``MathlibNt.ChensTheorem.chen_good_representations_lower_bound_unconditional]
  let env := (← getEnv).setExporting false
  for moduleName in env.header.moduleNames do
    let s := moduleName.toString
    if #["OAI", "ComparatorChallenges", "OpenAI"].any (fun p => s == p || s.startsWith (p ++ ".")) then
      throwError "Forbidden OpenAI import in audit environment: {moduleName}"
  let mut todo := audited.push ``ChenEffective.numericalSuzukiC1_single_exp_cap
  let mut seen : NameSet := {}
  let mut proofAxioms : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if forbidden.contains n then
      throwError "Circular use of an original implicit theorem: {n}"
    let some ci := env.find? n | throwError "Missing dependency: {n}"
    if ci.isUnsafe then throwError "Unsafe proof dependency: {n}"
    match ci with
    | .axiomInfo _ =>
      unless allowed.contains n do throwError "Unexpected traversed axiom: {n}"
      proofAxioms := proofAxioms.insert n
    | _ => pure ()
    todo := todo ++ ci.type.getUsedConstants
    if let some value := ci.value? (allowOpaque := true) then
      todo := todo ++ value.getUsedConstants
  unless proofAxioms.size == allowed.size do
    throwError "Traversed axiom count differs from the whitelist"
  logInfo m!"Proof dependency traversal passed ({seen.size} constants); no original implicit theorem used."
