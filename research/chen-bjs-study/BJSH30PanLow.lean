/- Threshold-specialized companion of research/chen-effective/NumericalPanLow.lean.
The original producer is retained; all modified numerical statements are rechecked. -/
import BJSH30PanPrimePrefix
import NumericalPanBudget
import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingLowEndpoint

noncomputable section
namespace ChenEffective.H30
open Classical Complex Finset
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def panLowConstant (U b : ℕ) : ℝ := 2*panMovingPrimeConstant b (U+b+2)+2
@[irreducible] def panLowThreshold (U b : ℕ) : ℕ :=
  max 9 (max (panMovingPrimeThreshold b (U+b+2)) (panBudgetThreshold U b))

theorem numerical_pan_low (U b N : ℕ) (hN : panLowThreshold U b ≤ N)
    (m A₁ A₂ Q : ℕ) (g : ℕ → ℂ)
    (hm : 1 ≤ m) (hmN : (m : ℝ) ≤ Real.sqrt N)
    (hA : (A₂ : ℝ) ≤ (N : ℝ)^(2/3 : ℝ))
    (hQ : (Q : ℝ) ≤ Real.log (N : ℝ)^b)
    (hg : ∀ a ∈ Ioc A₁ A₂, ‖g a‖ ≤ 1) :
    PanLow.nonprincipalLow g (fun n => if n.Prime ∧ n.Coprime m then 1 else 0)
      N A₁ A₂ Q ≤ panLowConstant U b*N/Real.log (N : ℝ)^U := by
  have hn := hN
  unfold panLowThreshold at hn
  obtain ⟨hN9, hrest⟩ := max_le_iff.mp hn
  obtain ⟨hpref, hpay⟩ := max_le_iff.mp hrest
  have hAN : A₂ ≤ N := by
    exact_mod_cast hA.trans (Real.rpow_le_self_of_one_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num))
  have hK : 0 ≤ panMovingPrimeConstant b (U+b+2) := by
    unfold panMovingPrimeConstant panPrimePrefixConstant primitiveNumericalConstant
    positivity
  have hh := PanLow.nonprincipalLow_le_prime_budget g N A₁ A₂ Q m
    (panMovingPrimeConstant b (U+b+2)) ((U+b+2 : ℕ) : ℝ)
    (by omega) hAN (by omega) hK hg (by
      intro a ha q hq χ
      obtain ⟨ha₁, ha₂⟩ := mem_Ioc.mp ha
      obtain ⟨hq₂, hqQ⟩ := mem_Icc.mp hq
      simpa only [Real.rpow_natCast] using numerical_prime_character_moving b (U+b+2) N hpref
        a (by omega) ((by exact_mod_cast ha₂ : (a : ℝ) ≤ A₂).trans hA) q hq₂
        ((by exact_mod_cast hqQ : (q : ℝ) ≤ Q).trans hQ) χ
        (primitiveCharacter_ne_one_of_two_le hq₂ χ))
  simp only [Real.rpow_natCast] at hh
  exact hh.trans (numerical_pan_budget U b N hpay _ hK m A₂ Q hm hmN hA hQ)

#print axioms numerical_pan_low
end ChenEffective.H30
