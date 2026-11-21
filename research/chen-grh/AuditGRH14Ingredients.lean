import GRHChenDistribution
import GRH14TripleBridge
import GRHSourceTail
import GRH14TruncationBudget
import GRHTruncatedSieveBounds
import Lean.Util.CollectAxioms

open Lean Meta

run_elab do
  if debug.skipKernelTC.get (← getOptions) then
    throwError "Kernel type checking must be enabled"
  let standard := #[``propext,``Classical.choice,``Quot.sound]
  let ax := ``ChenEffective.GRH.alpoge_dirichlet_grh
  let elementary := #[
    ``ChenEffective.GRH.preSieve_errSum_truncated,
    ``ChenEffective.GRH.prime_root_moment_four_million,
    ``ChenEffective.GRH.source_small_prime_divisor_moments,
    ``ChenEffective.GRH.source_rem_majorant,
    ``ChenEffective.GRH.source_presieve_rem_truncated,
    ``ChenEffective.GRH.truncated_preSieveCounting_lower_bound,
    ``ChenEffective.GRH.truncated_preSieveCounting_upper_bound,
    ``ChenEffective.GRH14.denominator_80323_at_target,
    ``ChenEffective.GRH14.truncated_moment_decay,
    ``ChenEffective.GRH14.truncation_tail_at_target,
    ``ChenEffective.GRH14.truncated_polynomial_payment,
    ``ChenEffective.GRH14.chen_of_lower_and_square]
  let conditional := #[``ChenEffective.GRH.chen_weighted_distribution]
  for n in elementary do
    let axs ← Lean.collectAxioms n
    unless axs.all standard.contains do
      throwError "Nonstandard axiom in elementary H14 ingredient {n}: {axs}"
  for n in conditional do
    let axs ← Lean.collectAxioms n
    unless axs.contains ax && axs.all (standard.push ax).contains do
      throwError "Unexpected axiom closure in GRH ingredient {n}: {axs}"
  let mut todo := elementary ++ conditional
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if #["sorryAx","Lean.ofReduceBool","Lean.trustCompiler"].contains n.toString then
      throwError "Forbidden proof dependency {n}"
    let some ci := (← getEnv).find? n | throwError "Missing dependency {n}"
    if ci.isUnsafe then throwError "Unsafe proof dependency {n}"
    if ci matches .axiomInfo _ then
      unless (standard.push ax).contains n do throwError "Unlisted axiom {n}"
    todo := todo ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then
      todo := todo ++ v.getUsedConstants
  logInfo m!"GRH H14 ingredient audit passed: {seen.size} transitive constants."
  logInfo "H14 remains conditional on the actual lower count and Selberg square estimates."
