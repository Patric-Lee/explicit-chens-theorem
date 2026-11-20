import BJSH29LowerCore
import PlattCertifiedPrefixWindow
import PlattAssumption

namespace ChenEffective.H29Conditional
instance : Fact HybridProduct.HybridPrefixWindow := ⟨PlattWindow.certified_prefix_window⟩
noncomputable abbrev chenCutoff : ℕ := H29Core.chenCutoff
theorem chenCutoff_eq : chenCutoff = 3^(3*10^12) := H29Core.chenCutoff_eq
theorem cutoff_lt_double_exp_29 : (chenCutoff:ℝ)<Real.exp (Real.exp (29:ℝ)) := by
  rw [chenCutoff_eq]
  exact H29.cutoff_lt_double_exp_29
theorem chen {N : ℕ} (hN : chenCutoff ≤ N) (hEven : Even N) :
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q :=
  H29Core.chen hN hEven
theorem original_chen : Goldbach.ChenTheorem :=
  ⟨chenCutoff, fun _ hN he => chen hN he⟩
#print axioms chen
#print axioms original_chen
end ChenEffective.H29Conditional
