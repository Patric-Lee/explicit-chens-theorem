import BJSStudyCompatibility
import BJSStudyH36
import BJSStudyFiniteTail
import BJSLayerQuadrature
import BJSLayerTwoSharp
import BJSSharpRecurrence
import Goldbach.Theorem
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean Meta
set_option maxHeartbeats 0

example : ChenEffective.bjsStudyN0=3^(3^171) := ChenEffective.bjsStudyN0_eq

example : ChenEffective.bjsStudyBudget.margin=(0.050585:ℝ) := by
  norm_num [ChenEffective.bjsStudyBudget,ChenEffective.ChenBudget.margin,
    ChenEffective.ChenBudget.weighted]

run_elab do
  if debug.skipKernelTC.get (← getOptions) then throwError "Kernel checking is disabled"
  unless ← isDefEq (← getConstInfo ``ChenEffective.bjsStudy_original_chen).type
      (← getConstInfo ``Goldbach.chen_theorem).type do
    throwError "Original Chen statement mismatch"
  logInfo "Provisional theorem recovers the exact original Chen statement."
  let standard := #[``propext,``Classical.choice,``Quot.sound]
  let provisional := #[``ChenEffective.bjsStudy_interval,
    ``ChenEffective.bjsStudy_lower_density,``ChenEffective.bjsStudy_upper_density]
  let allowed := standard ++ provisional ++ #[``ChenEffective.dirichlet_seven_eighths]
  for n in #[``ChenEffective.bjsStudy_chen,``ChenEffective.bjsStudy_original_chen] do
    let axs ← Lean.collectAxioms n
    unless axs.size == allowed.size && axs.all allowed.contains do
      throwError "Wrong provisional axiom ledger for {n}: {axs}"
  for n in #[``ChenEffective.bjsStudy_elementary_constant,
      ``ChenEffective.bjsStudy_reversed_interval_counterexample,
      ``ChenEffective.bjsStudy_layer_integral_grid,
      ``ChenEffective.bjsStudy_layer_successor_grid,
      ``ChenEffective.bjsStudy_layer_two_hat_sharp,
      ``ChenEffective.bjsStudy_source_hat_boundary,
      ``ChenEffective.bjsStudy_hat_tail_odd,
      ``ChenEffective.bjsStudy_even_error_coefficient,
      ``ChenEffective.bjsStudy_odd_error_coefficient,
      ``ChenEffective.bjsStudy_profile_forcing_cap,
      ``ChenEffective.bjsStudy_mertens_inverse,
      ``ChenEffective.bjsStudyCap_preSieve_base_distribution,
      ``ChenEffective.bjsStudyCap_preSieve_varying_threshold_cap,``ChenEffective.bjsStudy_log_six_sqrt,
      ``ChenEffective.bjsStudy_h36_geometry,``ChenEffective.bjsStudy_h36_margin,
      ``ChenEffective.bjsStudy_h36_lower_density_payment,
      ``ChenEffective.bjsStudy_h36_upper_density_payment,
      ``ChenEffective.bjsStudy_h36_base_payment,
      ``ChenEffective.bjsStudy_prefix_tail_certificate] do
    let axs ← Lean.collectAxioms n
    unless axs.all standard.contains do throwError "Unproved supporting result: {n}: {axs}"
  logInfo "Elementary replacements, H=36 scalar feasibility and finite-tail machinery use only standard axioms."
  logInfo "Ordered-interval regression, exact layer-two grid certificate, sharp hat bounds and recurrence caps use only standard axioms. Three provisional analytic inputs remain unproved."
  let forbidden := #[``Goldbach.chen_theorem,
    ``MathlibNt.ChensTheorem.chens_theorem_unconditional,
    `ChenEffective.qualitative_chen,`ChenEffective.qualitative_weighted_lower,
    `ChenEffective.qualitative_triple_bound,`ChenEffective.numerical_chen,
    `ChenEffective.numerical_chen_representation_count]
  let env := (← getEnv).setExporting false
  for m in env.header.moduleNames do
    if #["OpenAI","OAI","ComparatorChallenges"].any
        (fun s => m.toString == s || m.toString.startsWith (s++".")) then
      throwError "Forbidden import: {m}"
  let mut todo := #[``ChenEffective.bjsStudy_original_chen]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if forbidden.contains n then throwError "Old proof supplies provisional theorem: {n}"
    let some ci := env.find? n | throwError "Missing dependency: {n}"
    if ci.isUnsafe then throwError "Unsafe dependency: {n}"
    if ci matches .axiomInfo _ then
      unless allowed.contains n do throwError "Unlisted axiom: {n}"
    todo := todo ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque:=true) then todo := todo ++ v.getUsedConstants
  logInfo m!"Provisional proof traversal passed: {seen.size} constants; exactly three temporary BJS assumptions plus Dirichlet."
