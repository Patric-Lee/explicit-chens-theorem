import NumericalChenCompatibility
import NumericalC1SingleExponential
import NumericalSmallQuotientChen
import NumericalPolynomialChen
import NumericalDoubleExponential
import NumericalSeparateCoefficients
import NumericalEulerProductPower
import NumericalSieveErrorRecurrence
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
  let specializedBounds := #[
    ``ChenEffective.numerical_theta_power_error,
    ``ChenEffective.numerical_mertens_power,
    ``ChenEffective.goldbach_interval_power,
    ``ChenEffective.goldbach_presieved_small_error,
    ``ChenEffective.numerical_presieved_source_product,
    ``ChenEffective.presieve_log_cost,
    ``ChenEffective.specialized_sieve_error_sums,
    ``ChenEffective.specializedSieveError_certified]
  for n in specializedBounds do
    let axs ← Lean.collectAxioms n
    unless axs.all allowed.contains do
      throwError "Unexpected specialized sieve axioms for {n}: {axs}"
  for n in #[``ChenEffective.presieve_log_cost, ``ChenEffective.specializedSieveError_certified] do
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a && a != ``ChenEffective.dirichlet_seven_eighths) do
      throwError "Unexpected scalar or primorial axiom for {n}: {axs}"
  logInfo "Power-saving Euler products and coarse specialized recurrence passed the axiom whitelist."
  let audited : Array Name := #[
    ``ChenEffective.numerical_chen,
    ``ChenEffective.numerical_chen_representation_count,
    ``ChenEffective.numerical_chen_above_tower,
    ``ChenEffective.numerical_count_above_tower,
    ``ChenEffective.numerical_chen_above_double_exp,
    ``ChenEffective.numerical_count_above_double_exp,
    ``ChenEffective.numerical_implies_original_chen,
    ``ChenEffective.numerical_implies_original_internal_chen,
    ``ChenEffective.numerical_implies_original_representation_bound]
  for n in audited do
    let axs ← Lean.collectAxioms n
    unless axs.size == allowed.size && axs.all allowed.contains do
      throwError "Unexpected axioms for {n}: {axs}"
    logInfo m!"Exact four-axiom whitelist passed: {n}"
  for n in #[``ChenEffective.numerical_nLower_tower, ``ChenEffective.numerical_N0_tower,
      ``ChenEffective.numerical_nLower_double_exp, ``ChenEffective.numerical_N0_double_exp] do
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a && a != ``ChenEffective.dirichlet_seven_eighths) do
      throwError "Unexpected threshold axioms for {n}: {axs}"
  let terminalBounds := #[
    ``ChenEffective.numerical_actualT_le_exp_sourceL,
    ``ChenEffective.numerical_actualT_absolute_log_bound,
    ``ChenEffective.recursiveSmallMass_le_log,
    ``ChenEffective.numerical_small_quotient_sum_bound,
    ``ChenEffective.numerical_recursive_sum_split_absolute,
    ``ChenEffective.recursive_log_half,
    ``ChenEffective.recursiveSmallMass_eq_zero,
    ``ChenEffective.smallQuotient_single_exp_cap,
    ``ChenEffective.smallQuotient_terminal_single_exp_cap,
    ``ChenEffective.chenSmallQuotientCoefficient_cap,
    ``ChenEffective.chenSmallQuotientTerminalCoefficient_cap,
    ``ChenEffective.numerical_chen_small_quotient,
    ``ChenEffective.numerical_chen_small_quotient_sum,
    ``ChenEffective.numerical_actualT_polynomial_log_bound,
    ``ChenEffective.polynomialCorrection_recursive,
    ``ChenEffective.polynomialInheritedSum_high,
    ``ChenEffective.polynomialInheritedSum_caseII,
    ``ChenEffective.polynomial_compact_hat_floor,
    ``ChenEffective.polynomial_compact_correction_payment,
    ``ChenEffective.numerical_polynomial_transport_coarse,
    ``ChenEffective.polynomial_sourceSigma_gate,
    ``ChenEffective.polynomial_transport_level_gate,
    ``ChenEffective.numerical_polynomial_terminal_bound,
    ``ChenEffective.polynomialTerminalConstant_single_exp_cap,
    ``ChenEffective.polynomialClaimConstant_single_exp_cap,
    ``ChenEffective.numerical_chen_mixed_bounded,
    ``ChenEffective.numerical_mixed_suzuki,
    ``ChenEffective.numerical_mixed_caseI_cutoff,
    ``ChenEffective.numerical_mixed_even_cutoff,
    ``ChenEffective.mixed_caseII_from_cube,
    ``ChenEffective.numerical_mixed_suzuki_window,
    ``ChenEffective.numericalEffectiveSuzukiCoefficient_cap,
    ``ChenEffective.numerical_nLower_double_exp,
    ``ChenEffective.numerical_N0_double_exp,
    ``ChenEffective.numericalNLower_eq,
    ``ChenEffective.numericalN0_eq,
    ``ChenEffective.goldbach_interval_exponential,
    ``ChenEffective.goldbach_integer_product,
    ``ChenEffective.numerical_goldbach_split_interval,
    ``ChenEffective.numerical_refined_source_local_product,
    ``ChenEffective.numerical_exp_sqrt_round_bound,
    ``ChenEffective.numerical_chen_sqrt_suzuki_error,
    ``ChenEffective.mixed_claim_coefficient_sharp_cap,
    ``ChenEffective.mixed_low_strip_sharp_cap,
    ``ChenEffective.numericalEffectiveSuzukiCoefficient_sharp_cap,
    ``ChenEffective.relative_hat_unit_step,
    ``ChenEffective.relative_Qhat_unit_step,
    ``ChenEffective.relative_Qhat_initial_ratio,
    ``ChenEffective.numericalSuzukiC1_single_exp_sharp_cap,
    ``ChenEffective.strong_sourceSigma_gate,
    ``ChenEffective.strong_log_inverse_eighth,
    ``ChenEffective.numerical_separate_suzuki,
    ``ChenEffective.numerical_separate_suzuki_explicit,
    ``ChenEffective.unweighted_mixed_claim_coefficient]
  for n in #[``ChenEffective.numerical_mertens_all,
      ``ChenEffective.numerical_source_local_product,
      ``ChenEffective.numericalLocalProductK_eq,
      ``ChenEffective.numericalLocalProductK_lt,
      ``ChenEffective.numerical_Qhat_le_hat,
      ``ChenEffective.numerical_sharp_hat_profile,
      ``ChenEffective.caseBSourceC1_eq,
      ``ChenEffective.numericalSuzukiC1_single_exp_cap] ++ terminalBounds do
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a && a != ``ChenEffective.dirichlet_seven_eighths) do
      throwError "Unexpected elementary product axioms for {n}: {axs}"
  logInfo "Elementary Mertens, local-product, and improved C1 bounds use only standard axioms."
  logInfo "Absolute small-quotient and additive terminal bounds use only standard axioms."
  logInfo "Polynomial correction, natural-ceiling Case-I/II transport, gates, and bounded mixed branch use only standard axioms."
  logInfo "All-depth mixed induction, compact Case I, even endpoint, Case II, coefficient cap, and double-exponential cutoffs use only standard axioms."
  logInfo "Fixed-endpoint Euler-product split, K=10^12, square-root absorption, and sharp coefficient budgets use only standard axioms."
  logInfo "Separate hat/polynomial coefficients, the unweighted active profile, and its numerical gates use only standard axioms."
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
  let mut todo := (audited ++ terminalBounds ++ specializedBounds).push ``ChenEffective.numericalSuzukiC1_single_exp_cap
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
