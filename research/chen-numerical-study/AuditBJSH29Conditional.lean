import BJSH29ConditionalChen
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean Meta
set_option maxHeartbeats 0

example : ChenEffective.H29Conditional.chenCutoff=3^(3*10^12) :=
  ChenEffective.H29Conditional.chenCutoff_eq
example : (ChenEffective.H29Conditional.chenCutoff:ℝ)<Real.exp (Real.exp (29:ℝ)) :=
  ChenEffective.H29Conditional.cutoff_lt_double_exp_29
example : Goldbach.ChenTheorem := ChenEffective.H29Conditional.original_chen

-- This exact statement has no undisclosed prefix-window or counting premise.
example {N : ℕ} (hN : 3^(3*10^12)≤N) (hEven : Even N) :
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q := by
  apply ChenEffective.H29Conditional.chen ?_ hEven
  simpa only [ChenEffective.H29Conditional.chenCutoff_eq] using hN

example : ∀ ρ : ℂ, riemannZeta ρ=0 → 0<ρ.re → ρ.re<1 →
    |ρ.im|≤(100000000:ℝ) → ρ.re=1/2 :=
  ChenEffective.PlattWindow.platt_modulus_one_finite_RH

run_elab do
  if debug.skipKernelTC.get (← getOptions) then
    throwError "Kernel type checking must be enabled"
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let allowed := standard ++ #[``ChenEffective.PlattWindow.platt_modulus_one_finite_RH]
  for n in #[``ChenEffective.H29Conditional.chen,
      ``ChenEffective.H29Conditional.original_chen] do
    let axs ← Lean.collectAxioms n
    unless axs.size == allowed.size && axs.all allowed.contains do
      throwError "Wrong H29 axiom ledger for {n}: {axs}"
  for n in #[``ChenEffective.H29.fifth_triple_variable,
      ``ChenEffective.H29.chen_of_lower,
      ``ChenEffective.H29.cutoff_lt_double_exp_29,
      ``ChenEffective.H29.fixed_base_distribution,
      ``ChenEffective.H29Core.chen] do
    let axs ← Lean.collectAxioms n
    unless axs.all standard.contains do
      throwError "Unexpected axiom in generic or analytic producer {n}: {axs}"
  unless ← isDefEq (← getConstInfo ``ChenEffective.H29Conditional.original_chen).type
      (mkConst ``Goldbach.ChenTheorem) do
    throwError "Literal old Chen statement mismatch"
  let env ← getEnv
  let mut todo := #[``ChenEffective.H29Conditional.original_chen]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if #["Goldbach.chen_theorem",
        "MathlibNt.ChensTheorem.chens_theorem_unconditional",
        "ChenEffective.H30Conditional.chen", "ChenEffective.TightBudget.chen",
        "ChenEffective.H30.fifth_triple_closed",
        "ChenEffective.H30.numerical_pan_canonical",
        "ChenEffective.H30.numerical_pan_full_divisor",
        "ChenEffective.H30Conditional.temporary_reciprocal_prefix_window",
        "sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler"].contains n.toString then
      throwError "Forbidden shortcut or obsolete producer: {n}"
    let some ci := env.find? n | throwError "Missing dependency: {n}"
    if ci.isUnsafe then throwError "Unsafe dependency: {n}"
    if ci matches .axiomInfo _ then
      unless allowed.contains n do throwError "Unlisted axiom: {n}"
    todo := todo ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque:=true) then todo := todo ++ v.getUsedConstants
  for n in #[``ChenEffective.H29Conditional.chen,
      ``ChenEffective.H29Core.chen, ``ChenEffective.H29Core.weighted_lower,
      ``ChenEffective.H29Core.bjsStudy_base_candidates,
      ``ChenEffective.H29Core.bjsStudy_medium_prime_aggregate,
      ``ChenEffective.H29.presieve_shift_payment,
      ``ChenEffective.H29.fixed_base_distribution,
      ``ChenEffective.H29.weighted_distribution_paid,
      ``ChenEffective.H29.variable_margin,
      ``ChenEffective.H29.variable_triple_error_payment,
      ``ChenEffective.H29.variable_triple_envelope_cap,
      ``ChenEffective.H29.fifth_triple_variable,
      ``ChenEffective.H29.numerical_pan_full_divisor,
      ``ChenEffective.H29.numerical_pan_canonical,
      ``ChenEffective.H29.numerical_selberg_remainder,
      ``ChenEffective.H30.numerical_mertens_product,
      ``ChenEffective.bjsStudy_preSieveCounting_lower_bound,
      ``ChenEffective.bjsStudy_preSieveCounting_upper_bound,
      ``ChenEffective.PlattWindow.pointChainCertificate_sound,
      ``ChenEffective.PlattWindow.gridWindowCertificate_sound,
      ``ChenEffective.PlattWindow.certified_finite_relative_window,
      ``ChenEffective.PlattWindow.certified_prefix_window,
      ``OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re] do
    unless seen.contains n do throwError "Required actual producer missing: {n}"
  logInfo m!"Platt H29 Chen audit passed: {seen.size} transitive constants."
  logInfo "Cutoff 3^(3*10^12) is strictly below exp(exp(29)); literal original Chen recovered."
  logInfo "Exactly Platt modulus-one finite RH through 1e8 and standard Lean axioms."
  logInfo "Actual counts, sharper Mertens normalization, variable budget, and certified prefix window used."
