import Lean.Util.CollectAxioms
import GRH1337Analytic
import PlattCertifiedPrefixWindow
import PlattAssumption
import Goldbach.Statement

noncomputable section
namespace ChenEffective.GRH1337
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple

private instance : Fact HybridProduct.HybridPrefixWindow := ⟨PlattWindow.certified_prefix_window⟩
theorem weighted_lower {N : ℕ} (hN : targetCutoff≤N) (hEven : Even N) :
    (2.02575:ℝ)*(SingularSeries.liuSingularSeries N*N/Real.log (N:ℝ)^2)≤jurkatRichertWeightedCount N :=
  weighted_lower_of_window hN hEven


/-- Actual prime plus at-most-two-prime-factor representation at the explicit
cutoff. The complete lower and upper counting estimates supply all premises. -/
theorem chen {N : ℕ} (hN : targetCutoff≤N) (hEven : Even N) :
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q := by
  exact chen_of_weighted_lower hN hEven (weighted_lower hN hEven)

theorem chen_implicit : ∃ N₀ : ℕ, ∀ N : ℕ, N₀≤N → Even N →
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q :=
  ⟨targetCutoff,fun _ hN hEven => chen hN hEven⟩

/-- Literal recovery of the original repository's implicit Chen statement. -/
theorem original_chen : Goldbach.ChenTheorem :=
  ⟨targetCutoff,fun _ hN hEven => chen hN hEven⟩

theorem chen_of_double_exp_14 {N : ℕ}
    (hN : Real.exp (Real.exp (14:ℝ))≤N) (hEven : Even N) :
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q := by
  exact chen (target_of_double_exp_14 hN) hEven




theorem chen_explicit {N : ℕ} (hN : 3^580000≤N) (hEven : Even N) :
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q := by
  exact chen (by simpa only [targetCutoff_eq] using hN) hEven

theorem chen_of_double_exp_13_37 {N : ℕ}
    (hN : Real.exp (Real.exp (1337/100:ℝ))≤N) (hEven : Even N) :
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q := by
  have hh : targetCutoff≤N := by exact_mod_cast targetCutoff_lt_double_exp_13_37.le.trans hN
  exact chen hh hEven

end ChenEffective.GRH1337


open Lean Meta
run_elab do
  if debug.skipKernelTC.get (← getOptions) then
    throwError "Kernel type checking must be enabled"
  let standard := #[``propext,``Classical.choice,``Quot.sound]
  let ax := ``ChenEffective.GRH.alpoge_dirichlet_grh
  let roots := #[``ChenEffective.GRH1337.weighted_lower,
    ``ChenEffective.GRH1337.triple_upper,``ChenEffective.GRH1337.chen,
    ``ChenEffective.GRH1337.chen_implicit,``ChenEffective.GRH1337.original_chen,
    ``ChenEffective.GRH1337.chen_of_double_exp_14,
    ``ChenEffective.GRH1337.chen_explicit,``ChenEffective.GRH1337.chen_of_double_exp_13_37,
    ``ChenEffective.GRH1337.targetCutoff_lt_double_exp_13_37]
  let originalInfo ← getConstInfo ``ChenEffective.GRH1337.original_chen
  unless (← isDefEq originalInfo.type (mkConst ``Goldbach.ChenTheorem)) do
    throwError "Original Chen recovery has a different type"
  let axs ← Lean.collectAxioms ``ChenEffective.GRH1337.original_chen
  unless axs.contains ax && axs.all (standard.push ax).contains do
    throwError "Unexpected axiom closure of original Chen recovery: {axs}"
  logInfo m!"Original Chen axiom closure: {axs}"
  let mut todo := roots
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
  logInfo m!"GRH H1337 complete Chen audit passed: {seen.size} transitive constants."
  logInfo "Actual lower coefficient 2.02575 and triple coefficient 4.0002 at 3^580000."
  logInfo "Full explicit Chen existence and implicit recovery; sole added axiom is full Dirichlet GRH."
