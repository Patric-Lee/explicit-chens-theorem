import BJSH30ConditionalChen
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean Meta
set_option maxHeartbeats 0

example : ChenEffective.H30Conditional.chenCutoff = 3^(10^13) :=
  ChenEffective.H30Conditional.chenCutoff_eq

example : Goldbach.ChenTheorem := ChenEffective.H30Conditional.original_chen

example : (ChenEffective.jointSelbergBudget (82/10) (1/10000) 0 (1/1000)).margin =
    (0.005426:ℝ) := by
  rw [ChenEffective.joint_selberg_margin]
  norm_num

run_elab do
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let allowed := standard ++ #[
    ``ChenEffective.H30Conditional.temporary_reciprocal_prefix_window]
  for n in #[``ChenEffective.H30Conditional.chen,
      ``ChenEffective.H30Conditional.original_chen] do
    let axs ← Lean.collectAxioms n
    unless axs.size == allowed.size && axs.all allowed.contains do
      throwError "Wrong conditional theorem axiom ledger in {n}: {axs}"
  for n in #[``ChenEffective.H30Conditional.numerical_medium_prime_unshifted,
      ``ChenEffective.H30Conditional.numerical_medium_prime_shifted,
      ``ChenEffective.H30Conditional.preSieve_varying_paid,
      ``ChenEffective.H30.fifth_triple_closed] do
    let axs ← Lean.collectAxioms n
    unless axs.all standard.contains do
      throwError "Temporary numerical axiom leaked into independent analytic input {n}: {axs}"
  let env ← getEnv
  let mut todo := #[``ChenEffective.H30Conditional.original_chen]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if #["ChenEffective.TightBudget.chen", "ChenEffective.bjsStudy_chen",
        "sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler"].contains n.toString then
      throwError "Forbidden proof dependency: {n}"
    let some ci := env.find? n | throwError "Missing dependency: {n}"
    if ci.isUnsafe then throwError "Unsafe dependency: {n}"
    if ci matches .axiomInfo _ then
      unless allowed.contains n do throwError "Unlisted axiom: {n}"
    todo := todo ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque:=true) then todo := todo ++ v.getUsedConstants
  for n in #[``ChenEffective.H30Conditional.bjsStudy_base_candidates,
      ``ChenEffective.H30Conditional.bjsStudy_medium_prime_aggregate,
      ``ChenEffective.H30Conditional.preSieve_varying_paid,
      ``ChenEffective.H30Conditional.weighted_lower,
      ``ChenEffective.H30.fixed_base_distribution,
      ``ChenEffective.H30.numerical_source_mass_lower,
      ``ChenEffective.H30.numerical_source_mass_upper,
      ``ChenEffective.bjsStudy_preSieveCounting_lower_bound,
      ``ChenEffective.bjsStudy_preSieveCounting_upper_bound,
      ``ChenEffective.H30.fifth_triple_closed,
      ``ChenEffective.joint_selberg_existence] do
    unless seen.contains n do throwError "Required actual counting producer missing: {n}"
  unless seen.contains ``OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re do
    throwError "The actual proved OpenAI Dirichlet theorem is absent"
  logInfo m!"Conditional H30 Chen audit passed: {seen.size} transitive constants."
  logInfo "Exactly temporary_reciprocal_prefix_window and standard Lean axioms; Dirichlet is proved."
  logInfo "Actual lower/triple counts used; literal original implicit Chen statement recovered."
