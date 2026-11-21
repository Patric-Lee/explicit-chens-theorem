import GRHAssumption
import PlattAssumption
import Lean.Util.CollectAxioms

open Lean Meta

-- Exact released critical-strip GRH statement, with no finite-height restriction.
example : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2 :=
  ChenEffective.GRH.alpoge_dirichlet_grh

example : TernaryGoldbach.PlattZetaRH :=
  ChenEffective.PlattWindow.platt_modulus_one_finite_RH

run_elab do
  if debug.skipKernelTC.get (← getOptions) then
    throwError "Kernel type checking must be enabled"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound,
    ``ChenEffective.GRH.alpoge_dirichlet_grh]
  for n in #[``ChenEffective.GRH.zeta_finite_RH,
      ``ChenEffective.GRH.dirichlet_nonzero_right_in_strip,
      ``ChenEffective.PlattWindow.platt_modulus_one_finite_RH] do
    let axs ← Lean.collectAxioms n
    unless axs.contains ``ChenEffective.GRH.alpoge_dirichlet_grh && axs.all allowed.contains do
      throwError "Unexpected GRH consequence axioms for {n}: {axs}"
  let some ci := (← getEnv).find? ``ChenEffective.PlattWindow.platt_modulus_one_finite_RH |
    throwError "Missing finite-RH compatibility theorem"
  if ci matches .axiomInfo _ then throwError "Platt remains a separate axiom"
  logInfo "GRH assumption audit passed: exact full Dirichlet statement; finite RH is derived."

#print axioms ChenEffective.PlattWindow.platt_modulus_one_finite_RH
