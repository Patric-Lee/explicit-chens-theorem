import BJSStudyCompatibility
import BJSStudyH36
import BJSStudyFiniteTail
import BJSLayerQuadrature
import BJSLayerTwoSharp
import BJSSharpRecurrence
import BJSReciprocalLargeEndpoint
import BJSReciprocalRemainingRange
import BJSMertensThetaTarget
import Goldbach.Theorem
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean Meta
set_option maxHeartbeats 0

example : ChenEffective.bjsStudyN0=3^(3^2700) := ChenEffective.bjsStudyN0_eq

example : ChenEffective.bjsStudyBudget.margin=(0.050585:ℝ) := by
  norm_num [ChenEffective.bjsStudyBudget,ChenEffective.ChenBudget.margin,
    ChenEffective.ChenBudget.weighted]

run_elab do
  if debug.skipKernelTC.get (← getOptions) then throwError "Kernel checking is disabled"
  unless ← isDefEq (← getConstInfo ``ChenEffective.bjsStudy_original_chen).type
      (← getConstInfo ``Goldbach.chen_theorem).type do
    throwError "Original Chen statement mismatch"
  logInfo "The proved BJS theorem recovers the exact original Chen statement."
  let standard := #[``propext,``Classical.choice,``Quot.sound]
  let allowed := standard ++ #[``ChenEffective.dirichlet_seven_eighths]
  if ((← getEnv).find? `ChenEffective.bjsStudy_interval).isSome then
    throwError "The removed BJS interval axiom is still present in the environment"
  for n in #[``ChenEffective.bjsStudy_chen,``ChenEffective.bjsStudy_original_chen] do
    let axs ← Lean.collectAxioms n
    unless axs.size == allowed.size && axs.all allowed.contains do
      throwError "Wrong Dirichlet-only axiom ledger for {n}: {axs}"
  for n in #[``ChenEffective.bjsStudy_lower_density,``ChenEffective.bjsStudy_upper_density,
      ``ChenEffective.bjsSharpProfile_bound,``ChenEffective.bjsSharpError_finset_parity,
      ``ChenEffective.bjs_actual_source_layer_domination,
      ``ChenEffective.bjs_actual_source_parity_domination,
      ``ChenEffective.bjsStudy_elementary_constant,
      ``ChenEffective.bjsStudy_reversed_interval_counterexample,
      ``ChenEffective.bjsStudy_layer_integral_grid,
      ``ChenEffective.bjsStudy_layer_successor_grid,
      ``ChenEffective.bjsStudy_layer_two_hat_sharp,
      ``ChenEffective.bjsStudy_source_hat_boundary,
      ``ChenEffective.bjsStudy_hat_tail_odd,
      ``ChenEffective.bjsStudy_even_error_coefficient,
      ``ChenEffective.bjsStudy_odd_error_coefficient,
      ``ChenEffective.bjsStudy_profile_forcing_cap,
      ``ChenEffective.bjsStudy_interval_prefix_disjoint,
      ``ChenEffective.bjsStudy_interval_of_prefix,
      ``ChenEffective.bjsStudy_interval_of_half_log_squared_prefix,
      ``ChenEffective.bjsStudy_power_error_log_squared,
      ``ChenEffective.bjsStudy_canonical_mertens_upper,
      ``ChenEffective.bjsLogUpper_valid,
      ``ChenEffective.bjsSmallPrefixCertificates,
      ``ChenEffective.bjsSmallSignedPrefix_lower,
      ``ChenEffective.bjsStudy_power_error_log_squared_3300,
      ``ChenEffective.bjsStudy_log_three_lower,
      ``ChenEffective.bjsStudyProductProfile,
      ``ChenEffective.bjsStudy_product_error_cap,
      ``ChenEffective.bjsStudy_mertens_of_theta_target,
      ``ChenEffective.bjsStudy_theta_target_payment,
      ``ChenEffective.bjsStudy_prefix_at_presieve_of_theta_target,
      ``ChenEffective.bjsStudy_interval_prefix_composite,
      ``ChenEffective.bjsStudy_presieve_interval_of_theta_target,
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
  let dirichletOnly := standard ++ #[``ChenEffective.dirichlet_seven_eighths]
  for n in #[``ChenEffective.bjsStudy_interval_product,
      ``ChenEffective.bjsStudy_presieved_product,
      ``ChenEffective.bjsStudy_product_relative,
      ``ChenEffective.bjsStudy_weighted_lower,
      ``ChenEffective.bjsStudy_triple_bound,
      ``ChenEffective.bjsStudy_interval_power,
      ``ChenEffective.bjsStudy_reciprocal_prefix_large,
      ``ChenEffective.bjsStudy_interval_large_endpoint,
      ``ChenEffective.bjsStudy_interval_of_middle_prefix,
      ``ChenEffective.bjsStudy_reciprocal_prefix_from_3300,
      ``ChenEffective.bjsStudy_reciprocal_prefix_from_3072,
      ``ChenEffective.bjsStudy_interval_from_3072,
      ``ChenEffective.bjsStudy_interval_of_remaining_prefix] do
    let axs ← Lean.collectAxioms n
    unless axs.size == dirichletOnly.size && axs.all dirichletOnly.contains do
      throwError "Product, counting or interval result has the wrong axiom ledger: {n}: {axs}"
  logInfo "The active product profile at 3^2652, lower count, triple bound and Chen theorem use only Dirichlet plus standard axioms. No BJS axiom remains."
  logInfo "Finite lower prefix through 286 uses only standard axioms. Signed tail and interval from 3^3072 use Dirichlet only. The intervening signed-prefix range, including 3^120, remains unproved."
  logInfo "The theta-to-prefix and closed-left interval bridges at 3^120 use only standard axioms; the theta hypothesis itself has NOT been proved or added as an axiom."
  logInfo "Both BJS density adapters and their complete analytic/discrete proof chain use only standard axioms. The low-endpoint theta studies are retained separately from the active proof."
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
    if forbidden.contains n then throwError "Old proof supplies the BJS theorem: {n}"
    let some ci := env.find? n | throwError "Missing dependency: {n}"
    if ci.isUnsafe then throwError "Unsafe dependency: {n}"
    if ci matches .axiomInfo _ then
      unless allowed.contains n do throwError "Unlisted axiom: {n}"
    todo := todo ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque:=true) then todo := todo ++ v.getUsedConstants
  logInfo m!"BJS proof traversal passed: {seen.size} constants; exactly Dirichlet plus standard axioms, with no original implicit Chen proof."
