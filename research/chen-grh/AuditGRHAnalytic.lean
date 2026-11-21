import AuditGRHAssumption
import GRHCharacterConstants
import GRH14SelbergBudget
import GRH14ScalarBudget
import GRHWeightedDistribution
import Lean.Util.CollectAxioms

open Lean Meta

run_elab do
  if debug.skipKernelTC.get (← getOptions) then
    throwError "Kernel type checking must be enabled"
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let ax := ``ChenEffective.GRH.alpoge_dirichlet_grh
  let unconditional := #[``ChenEffective.GRH.absolute_zero_sum_finite_RH,
    ``ChenEffective.GRH.gaussian_constant_cap,
    ``ChenEffective.GRH14.targetCutoff_lt_double_exp_14,
    ``ChenEffective.GRH14.polynomial_error_payment,
    ``ChenEffective.GRH14.distribution_error_payment,
    ``ChenEffective.GRH14.small_start_requires_larger_product_allowance,
    ``ChenEffective.GRH.logDerivative_disk_gap,
    ``ChenEffective.GRH.smoothed_mellin_min,
    ``ChenEffective.GRH.perron_left_logarithmic,
    ``ChenEffective.GRH.perron_envelope_payment,
    ``ChenEffective.GRH.chebyshev_AP_trivial,
    ``ChenEffective.GRH.three_omega_mass,
    ``ChenEffective.GRH14.representation_of_target_counts,
    ``ChenEffective.GRH14.denominator_at_target]
  let conditional := #[``ChenEffective.GRH.zero_sum_full_GRH,
    ``ChenEffective.GRH.smoothed_character_full_GRH,
    ``ChenEffective.GRH.gaussian_character_numerical,
    ``ChenEffective.GRH.logDerivative_strip_gap,
    ``ChenEffective.GRH.zeta_logDerivative_gap,
    ``ChenEffective.GRH.smoothed_perron_bound,
    ``ChenEffective.GRH.principal_smoothed_bound,
    ``ChenEffective.GRH.nonprincipal_prefix_numerical,
    ``ChenEffective.GRH.principal_prefix_numerical,
    ``ChenEffective.GRH.chebyshev_AP_numerical,
    ``ChenEffective.GRH.chebyshev_AP_max_numerical,
    ``ChenEffective.GRH.prime_AP_max_numerical,
    ``ChenEffective.GRH.weighted_AP_numerical]
  for n in unconditional do
    let axs ← Lean.collectAxioms n
    unless axs.all standard.contains do
      throwError "Nonstandard axiom in generic numerical bound {n}: {axs}"
  for n in conditional do
    let axs ← Lean.collectAxioms n
    unless axs.contains ax && axs.all (standard.push ax).contains do
      throwError "Unexpected full-GRH analytic axiom closure {n}: {axs}"
  let mut todo := unconditional ++ conditional
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if #["sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler"].contains n.toString then
      throwError "Forbidden proof dependency {n}"
    let some ci := (← getEnv).find? n | throwError "Missing dependency {n}"
    if ci.isUnsafe then throwError "Unsafe proof dependency {n}"
    if ci matches .axiomInfo _ then
      unless (standard.push ax).contains n do throwError "Unlisted axiom {n}"
    todo := todo ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then
      todo := todo ++ v.getUsedConstants
  logInfo m!"GRH analytic audit passed: {seen.size} transitive constants."
  logInfo "Generic numerical and Selberg bounds are standard-only; character sums use exactly full Dirichlet GRH."
  logInfo "H14 is a checked scalar target and conditional counting bridge, not a completed Chen theorem."
