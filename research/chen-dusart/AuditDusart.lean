import DusartPort.Application
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean Meta
set_option maxHeartbeats 0

run_elab do
  if debug.skipKernelTC.get (← getOptions) then throwError "Kernel checking is disabled"
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let allowed := standard
  for n in #[``ChenEffective.dusart_xi_zero_moment_identity,
      ``ChenEffective.dusart_zeta_zero_multiplicity,
      ``ChenEffective.Dusart.numerical_unsmoothing,
      ``ChenEffective.Dusart.theta_of_numerical_psi,
      ``DusartPort.Lab.ExplicitPsi1.explicit_formula_psi1,
      ``DusartPort.Lab.ExplicitPsi1.Trivial.explicit_formula_psi1_trivial] do
    let axs ← Lean.collectAxioms n
    unless axs.all standard.contains do throwError "Unproved analytic foundation: {n}: {axs}"
  let roots := #[``ChenEffective.dusart_xi_zero_absolute_moment,
    ``ChenEffective.dusart_zeta_zero_absolute_moment,
    ``ChenEffective.Dusart.numerical_psi1,
    ``ChenEffective.Dusart.numerical_theta_target,
    ``ChenEffective.dusart_theta_from_presieve,
    ``ChenEffective.dusart_sharp_mertens,
    ``ChenEffective.dusart_sharp_prime_interval]
  for n in roots do
    let axs ← Lean.collectAxioms n
    unless axs.size == allowed.size && axs.all allowed.contains do
      throwError "Wrong standard-only axiom ledger: {n}: {axs}"
  let env := (← getEnv).setExporting false
  for m in env.header.moduleNames do
    if m.toString == "ComparatorChallenges" || m.toString.startsWith "ComparatorChallenges." then
      throwError "Forbidden import: {m}"
  let mut todo := roots
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "Missing proof dependency: {n}"
    if ci.isUnsafe then throwError "Unsafe proof dependency: {n}"
    if ci matches .axiomInfo _ then
      unless allowed.contains n do throwError "Unlisted axiom: {n}"
    todo := todo ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then todo := todo ++ v.getUsedConstants
  unless seen.contains ``OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re do
    throwError "Actual proved Dirichlet theorem absent"
  logInfo m!"Dusart proof traversal passed: {seen.size} constants; standard axioms only; Dirichlet is proved."
  logInfo "The theta estimate and sharp signed prefix and closed-left prime interval bounds are proved from 3^120, without finite-height RH or a numerical zero table."
