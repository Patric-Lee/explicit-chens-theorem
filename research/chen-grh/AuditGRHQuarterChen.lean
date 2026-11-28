import Lean.Util.CollectAxioms
import GRHQuarterChenAnalytic
import GRHQuarterChenEndpoint
import PlattCertifiedPrefixWindow
import PlattAssumption
import Goldbach.Statement

noncomputable section
namespace ChenEffective.GRHQuarterChen
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple

private instance : Fact HybridProduct.HybridPrefixWindow :=
  ⟨PlattWindow.certified_prefix_window⟩

theorem weighted_lower {N : ℕ} (hN : targetCutoff≤N) (hEven : Even N) :
    (2.00825:ℝ)*(SingularSeries.liuSingularSeries N*N/Real.log (N:ℝ)^2)≤
      jurkatRichertWeightedCount N := weighted_lower_of_window hN hEven

theorem chen {N : ℕ} (hN : targetCutoff≤N) (hEven : Even N) :
    ∃ p q : ℕ,p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ,r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q :=
  chen_of_weighted_lower hN hEven (weighted_lower hN hEven)

theorem chen_explicit {N : ℕ} (hN : 3^119081≤N) (hEven : Even N) :
    ∃ p q : ℕ,p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ,r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q :=
  chen (by simpa only [targetCutoff_eq] using hN) hEven

theorem original_chen : Goldbach.ChenTheorem :=
  ⟨targetCutoff,fun _ hN hEven=>chen hN hEven⟩

theorem chen_implicit : ∃ N₀ : ℕ,∀ N : ℕ,N₀≤N → Even N →
    ∃ p q : ℕ,p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ,r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q :=
  original_chen

theorem chen_of_double_exp_11782 {N : ℕ}
    (hN : Real.exp (Real.exp (5891/500:ℝ))≤N) (hEven : Even N) :
    ∃ p q : ℕ,p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ,r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q := by
  apply chen (hEven:=hEven)
  exact_mod_cast targetCutoff_lt_double_exp_11782.le.trans hN

theorem representation_margin : (2.00825:ℝ)-4.015/2=3/4000 := by norm_num

#check chen_explicit
#check original_chen
#check chen_of_double_exp_11782
end ChenEffective.GRHQuarterChen
end




open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
private def expectedExplicitChen : Prop := ∀ {N : ℕ},3^119081≤N → Even N →
  ∃ p q : ℕ,p.Prime ∧ (q.Prime ∨ ∃ r s : ℕ,r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q
private def expectedLower : Prop := ∀ {N : ℕ},ChenEffective.GRHQuarterChen.targetCutoff≤N → Even N →
  (2.00825:ℝ)*(SingularSeries.liuSingularSeries N*N/Real.log (N:ℝ)^2)≤jurkatRichertWeightedCount N
private def expectedTriple : Prop := ∀ {N : ℕ},ChenEffective.GRHQuarterChen.targetCutoff≤N → Even N →
  correctedChenTriplePenalty N≤(4.015:ℝ)*(SingularSeries.liuSingularSeries N*N/Real.log (N:ℝ)^2)
private def expectedCutoff : Prop := ChenEffective.GRHQuarterChen.targetCutoff=3^119081
private def expectedEndpoint : Prop := (ChenEffective.GRHQuarterChen.targetCutoff:ℝ)<Real.exp (Real.exp (5891/500:ℝ))

open Lean Meta
set_option maxHeartbeats 0
run_elab do
  if debug.skipKernelTC.get (← getOptions) then
    throwError "Kernel checking must be enabled"
  let standard := #[``propext,``Classical.choice,``Quot.sound]
  let ax := ``ChenEffective.GRH.alpoge_dirichlet_grh
  let allowed := standard.push ax
  let roots := #[``ChenEffective.GRHQuarterChen.weighted_lower,
    ``ChenEffective.GRHQuarterChen.triple_upper,
    ``ChenEffective.GRHQuarterChen.chen_explicit,
    ``ChenEffective.GRHQuarterChen.original_chen,
    ``ChenEffective.GRHQuarterChen.chen_of_double_exp_11782,
    ``ChenEffective.GRHQuarterChen.source_accuracy_exponent_minimal]
  let original ← getConstInfo ``ChenEffective.GRHQuarterChen.original_chen
  unless (← isDefEq original.type (mkConst ``Goldbach.ChenTheorem)) do
    throwError "Original Chen statement has changed"
  for (actual,expected) in #[(``ChenEffective.GRHQuarterChen.chen_explicit,``expectedExplicitChen),
      (``ChenEffective.GRHQuarterChen.weighted_lower,``expectedLower),
      (``ChenEffective.GRHQuarterChen.triple_upper,``expectedTriple),
      (``ChenEffective.GRHQuarterChen.targetCutoff_eq,``expectedCutoff),
      (``ChenEffective.GRHQuarterChen.targetCutoff_lt_double_exp_11782,``expectedEndpoint)] do
    let info ← getConstInfo actual
    unless (← isDefEq info.type (mkConst expected)) do
      throwError "Numerical Chen statement changed: {actual}"
  logInfo "Literal cutoff, lower/triple coefficients, and H endpoint types checked."
  let mut seen : NameSet := {}
  let mut axioms : Array Name := #[]
  -- Check the original statement first, then extend the same complete
  -- traversal to the component roots. Mark on enqueue to bound the queue.
  for phase in #[#[``ChenEffective.GRHQuarterChen.original_chen],roots] do
    let mut todo : Array Name := #[]
    for root in phase do
      unless seen.contains root do
        seen := seen.insert root
        todo := todo.push root
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if #["sorryAx","Lean.ofReduceBool","Lean.trustCompiler",
        "ChenEffective.GRHSub13.pan_prime_moving","ChenEffective.GRHSub13.pan_principal_moving",
        "ChenEffective.GRHSub13.pan_moving_power_payment","ChenEffective.numerical_low_prefix_power"].contains n.toString then
        throwError "Forbidden proof dependency {n}"
      let some ci := (←getEnv).find? n | throwError "Missing proof dependency {n}"
      if ci.isUnsafe then throwError "Unsafe proof dependency {n}"
      if ci matches .axiomInfo _ then
        unless allowed.contains n do throwError "Unlisted axiom {n}"
        axioms := axioms.push n
      let mut deps := ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque:=true) then
        deps := deps ++ v.getUsedConstants
      for d in deps do
        unless seen.contains d do
          seen := seen.insert d
          todo := todo.push d
    if phase.size==1 then
      unless axioms.contains ax do throwError "Original Chen GRH dependency missing"
      logInfo m!"Quarter Chen axiom closure: {axioms}"
  logInfo m!"Quarter Chen full audit passed: {seen.size} transitive constants."
  logInfo "Exact cutoff 3^119081; H < 11.782; lower 2.00825; triple 4.015; margin 3/4000."
  logInfo "Literal original Chen recovery checked; full Dirichlet GRH is the sole added axiom."
