import BJSH30FifthTriple
import BJSH30SmallEndpoint
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean Meta
set_option maxHeartbeats 0

example : ChenEffective.H30.squareClosedThreshold=3^(5*10^12) :=
  ChenEffective.H30.squareClosedThreshold_eq

example : (ChenEffective.jointSelbergBudget (82/10) (1/10000) 0 (1/1000)).margin=
    (0.005426 : ℝ) := by
  rw [ChenEffective.joint_selberg_margin]
  norm_num

run_elab do
  let standard := #[``propext,``Classical.choice,``Quot.sound]
  let allowed := standard
  for n in #[``ChenEffective.H30.fifth_square_error_cap,
      ``ChenEffective.H30.fifth_analytic_cap] do
    let axs ← Lean.collectAxioms n
    unless axs.all standard.contains do throwError "Nonstandard scalar axiom in {n}: {axs}"
  for n in #[``ChenEffective.H30.fifth_triple_closed,
      ``ChenEffective.H30.chen_of_lower,
      ``ChenEffective.H30.small_endpoint_interval_product] do
    let axs ← Lean.collectAxioms n
    unless axs.size == allowed.size && axs.all allowed.contains do
      throwError "Wrong analytic axiom ledger in {n}: {axs}"
  let env ← getEnv
  let forbidden := #["ChenEffective.H30.joint_triple_closed",
    "ChenEffective.TightBudget.chen","ChenEffective.bjsStudy_chen"]
  let mut todo := #[``ChenEffective.H30.chen_of_lower]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if forbidden.contains n.toString then throwError "Old triple/final theorem used: {n}"
    let some ci := env.find? n | throwError "Missing dependency: {n}"
    if ci.isUnsafe then throwError "Unsafe dependency: {n}"
    if ci matches .axiomInfo _ then
      unless allowed.contains n do throwError "Unlisted axiom: {n}"
    todo := todo ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque:=true) then todo := todo ++ v.getUsedConstants
  for n in #[``ChenEffective.H30.fifth_selberg_square,
      ``ChenEffective.H30.fifth_error_payment,
      ``ChenEffective.H30.numerical_selberg_remainder,
      ``ChenEffective.H30.numerical_prime_pair_main,
      ``MathlibNt.SieveTheory.LiuWeight.liuSelbergCorrectedSourceTripleCount_le_square_add_QResidual,
      ``ChenEffective.explicit_triple_complement,
      ``ChenEffective.explicit_triple_paper_residual] do
    unless seen.contains n do throwError "Required actual upper-count producer missing: {n}"
  logInfo m!"H30 complete triple audit passed: {seen.size} constants; standard axioms only; Dirichlet is proved."
  logInfo "Square error C5/log^5 plus the actual 19/log^3 complement is paid by 0.001*S/log^2."
  logInfo "Small-endpoint product theorem is conditional on SmallEndpointPrefixWindow; that proposition has NOT been proved."

