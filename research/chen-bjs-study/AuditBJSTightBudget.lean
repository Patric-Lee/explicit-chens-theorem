import BJSTightChen
import BJSH30MassCap
import BJSH30BaseDistribution
import BJSH30Geometry
import BJSH30Budget
import BJSExpandedChen
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean Meta
set_option maxHeartbeats 0

example : ChenEffective.TightBudget.chenCutoff=3^(3^134) :=
  ChenEffective.TightBudget.chenCutoff_eq
example : ChenEffective.H30.squareClosedThreshold=3^(5*10^12) :=
  ChenEffective.H30.squareClosedThreshold_eq

run_elab do
  let standard := #[``propext,``Classical.choice,``Quot.sound]
  let allowed := standard
  for n in #[``ChenEffective.H30.source_modulus_of_log,
      ``ChenEffective.H30.ratio_shift_near_H30,
      ``ChenEffective.H30.numerical_square_analytic_cap,
      ``ChenEffective.H30.expanded_selberg_denominator,
      ``ChenEffective.H30.medium_mass_allocation,
      ``ChenEffective.H30.target_margin,
      ``ChenEffective.TightBudget.chosen_margin] do
    let axs ← Lean.collectAxioms n
    unless axs.all standard.contains do throwError "Nonstandard scalar/component axiom in {n}: {axs}"
  for n in #[``ChenEffective.TightBudget.chen,
      ``ChenEffective.H30.numerical_prime_pair_main,
      ``ChenEffective.H30.source_mass_at_closed_threshold,
      ``ChenEffective.H30.base_distribution_paid,
      ``ChenEffective.H30.varying_distribution_paid] do
    let axs ← Lean.collectAxioms n
    unless axs.size == allowed.size && axs.all allowed.contains do
      throwError "Wrong analytic axiom ledger in {n}: {axs}"
  let env ← getEnv
  let forbidden := #[``ChenEffective.bjsStudy_chen,``ChenEffective.joint_chen_81,
    ``ChenEffective.expanded_chen]
  let mut todo := #[``ChenEffective.TightBudget.original_chen]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if forbidden.contains n then throwError "Old final proof used: {n}"
    let some ci := env.find? n | throwError "Missing dependency: {n}"
    if ci.isUnsafe then throwError "Unsafe dependency: {n}"
    if ci matches .axiomInfo _ then
      unless allowed.contains n do throwError "Unlisted axiom: {n}"
    todo := todo ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque:=true) then todo := todo ++ v.getUsedConstants
  for n in #[``ChenEffective.H30.numerical_prime_character_moving,
      ``ChenEffective.H30.numerical_prime_pair_main,
      ``ChenEffective.H30.numerical_source_mass_lower,
      ``ChenEffective.H30.numerical_source_mass_upper,
      ``ChenEffective.selberg_uniform_two_term_expansion] do
    unless seen.contains n do throwError "Expected improved producer is missing: {n}"
  unless seen.contains ``OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re do
    throwError "The actual proved OpenAI Dirichlet theorem is absent"
  logInfo m!"Tight-budget final proof audit passed: {seen.size} constants; standard axioms only; Dirichlet is proved."
  logInfo "Final cutoff 3^(3^134), K=8.2, epsilon=1/100; original literal Chen statement recovered."
  logInfo "Near-H=30 source mass, base/varying distribution, prime-pair main term, square analytic cap and scalar geometry are checked separately; no full H=30 Chen theorem is asserted."
