import BJSSelbergSquareRemainder
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean Meta
set_option maxHeartbeats 0

run_elab do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  let roots := #[``ChenEffective.selberg_signed_log_moment,
    ``ChenEffective.selberg_two_term_identity,
    ``ChenEffective.square_harmonic_mass,
    ``ChenEffective.selberg_square_residual_mass,
    ``ChenEffective.selberg_correction_square_convolution,
    ``ChenEffective.selberg_critical_half_mass,
    ``ChenEffective.selberg_two_term_sqrt_remainder,
    ``ChenEffective.selberg_uniform_two_term_expansion]
  let env ← getEnv
  let mut todo := roots
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "Missing dependency: {n}"
    if ci.isUnsafe then throwError "Unsafe dependency: {n}"
    if ci matches .axiomInfo _ then
      unless allowed.contains n do throwError "Unlisted axiom: {n}"
    todo := todo ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque:=true) then todo := todo ++ v.getUsedConstants
  for n in roots do
    let axs ← Lean.collectAxioms n
    unless axs.all allowed.contains do throwError "Nonstandard axiom in {n}: {axs}"
  logInfo m!"Selberg two-term expansion audit passed: {seen.size} constants; standard axioms only."
