import BJSJointChen
import Goldbach.Theorem
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean Meta
set_option maxHeartbeats 0

example : ChenEffective.jointSelbergDenominatorThreshold=3^(3^83) :=
  ChenEffective.jointSelbergDenominatorThreshold_eq

run_elab do
  let standard := #[``propext,``Classical.choice,``Quot.sound]
  let allowed := standard
  for n in #[``ChenEffective.selberg_specialized_prime_expansion,
      ``ChenEffective.selberg_specialized_secondary_cancellation,
      ``ChenEffective.selberg_specialized_normalized_nondisor,
      ``ChenEffective.selberg_specialized_normalized_divisor,
      ``ChenEffective.selberg_specialized_divisor_ratio,
      ``ChenEffective.selberg_specialized_secondary_pos,
      ``ChenEffective.selberg_denominator_from_joint_error,
      ``ChenEffective.joint_selberg_denominator_81,
      ``ChenEffective.joint_selberg_existence,
      ``ChenEffective.joint_selberg_81_margin,
      ``ChenEffective.joint_selberg_82_margin] do
    let axs ← Lean.collectAxioms n
    unless axs.all standard.contains do throwError "Nonstandard axiom in {n}: {axs}"
  let axs ← Lean.collectAxioms ``ChenEffective.joint_chen_81
  unless axs.size == allowed.size && axs.all allowed.contains do
    throwError "Wrong final joint axiom ledger: {axs}"
  let env ← getEnv
  let forbidden := #[``ChenEffective.bjsStudy_chen,``Goldbach.chen_theorem]
  let mut todo := #[``ChenEffective.joint_chen_81]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if forbidden.contains n then throwError "Old final proof supplies the joint result: {n}"
    let some ci := env.find? n | throwError "Missing dependency: {n}"
    if ci.isUnsafe then throwError "Unsafe dependency: {n}"
    if ci matches .axiomInfo _ then
      unless allowed.contains n do throwError "Unlisted axiom: {n}"
    todo := todo ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque:=true) then todo := todo ++ v.getUsedConstants
  logInfo m!"Joint proof traversal passed: {seen.size} constants; Dirichlet plus standard axioms only."
  logInfo "Relaxed denominator cutoff 3^(3^83) and budget allocation proved; final Chen cutoff remains 3^(3^171)."
